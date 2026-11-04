UptimeGraphs = {}
local UG = UptimeGraphs

local NAME, VERSION = "UptimeGraphs", "1.1.0"
local EM            = EVENT_MANAGER
local GetTimeMs     = GetGameTimeMilliseconds

local DEFAULTS = { maxEncounters = 20, useComposite = true, compare = false, w = 780, h = 660 }

-- capture
local STRIDE       = 5                  -- t, abilityId, unitKey, changeType, endTime
local MAX_SLOTS    = STRIDE * 60000     -- hard cap on the raw buffer (~60k events)
local END_DELAY_MS = 2000               -- out-of-combat debounce
local MIN_FIGHT_MS = 3000               -- discard shorter sessions
local BOSS_TAGS    = { "boss1", "boss2", "boss3", "boss4", "boss5", "boss6" }
local HOTBARS      = { HOTBAR_CATEGORY_PRIMARY, HOTBAR_CATEGORY_BACKUP, HOTBAR_CATEGORY_OVERLOAD, HOTBAR_CATEGORY_WEREWOLF }

-- layout (pixels)
local ROW_TYPE, ROW_H = 1, 30
local PAD = 12
local ROW_LEFT, ROW_RIGHT, BAR_H = 292, 6, 20   -- ROW_LEFT = icon + name + pct columns before the bar (see UG_Row)
local AXIS_Y, LABEL_Y, LIST_TOP, SECTION_GAP = 68, 92, 112, 34
local INFO_LEFT = 128                           -- x where the Info label starts
-- Solid, tintable region of ZOS's own dye-swatch sheet (ZOS tints it with SetColor too). Sampled from its centre.
local TC_L, TC_R, TC_T, TC_B = 0.09, 0.16, 0.09, 0.16

-- comparison mode: previous parse is drawn in blue under each row; a side panel lists the change
local COMPARE_W = 220                                        -- header space reserved for the checkbox + its label
local PANEL_W, PANEL_GAP, PROW_H = 330, 12, 26
local P_PAD, P_LIST_TOP, P_SECTION_GAP = 10, 84, 34
local COL_CUR,  COL_PREV  = { 0.25, 0.80, 0.45 }, { 0.30, 0.55, 1.00 }   -- bar colours (green = this parse, blue = previous)
local TXT_CUR,  TXT_PREV  = { 1, 1, 1 },          { 0.62, 0.77, 1.00 }
local DELTA_UP, DELTA_DOWN, DELTA_FLAT = { 0.35, 0.90, 0.45 }, { 1.00, 0.40, 0.40 }, { 0.72, 0.72, 0.72 }
local DELTA_EPS = 0.0005                                     -- changes under 0.05 points count as "no change"
local EMPTY = {}

local buf, n = {}, 0
local logging, manual = false, false
local startMs, combatEndMs, startTime, zoneName, bossName, slotted
local encounters, selected = {}, 0
local viewed, shown                        -- encounter selected / encounter the lists were last filled from
local barW = 380
local sv

local function Say(msg) CHAT_ROUTER:AddSystemMessage("|c66ccff[Uptimes]|r " .. msg) end

-- Anything the player triggers runs through this so a failure is printed instead of vanishing.
local function Guard(fn)
    return function(...)
        if UG.initError then
            Say("|cff6666failed to initialize:|r " .. UG.initError)
            return
        end
        local ok, err = pcall(fn, ...)
        if not ok then Say("|cff6666error:|r " .. tostring(err)) end
    end
end

-------------------------------------------------------------------------------
-- Capture: raw append only. No tables created, no lookups, no math.
-------------------------------------------------------------------------------
local function OnEffect(_, change, _, _, unitTag, _, endTime, _, _, _, _, _, _, _, unitId, abilityId)
    if n >= MAX_SLOTS then return end
    buf[n + 1] = GetTimeMs()
    buf[n + 2] = abilityId
    buf[n + 3] = (unitTag == "player") and 0 or unitId
    buf[n + 4] = change
    buf[n + 5] = endTime
    n = n + STRIDE
end

-- fires rarely (boss list changes); lets encounters be labelled
local function OnBossesChanged()
    if bossName then return end
    for i = 1, #BOSS_TAGS do
        local tag = BOSS_TAGS[i]
        if DoesUnitExist(tag) then
            local nm = zo_strformat(SI_UNIT_NAME, GetUnitName(tag))
            if nm ~= "" then bossName = nm; return end
        end
    end
end

-------------------------------------------------------------------------------
-- Classification: which abilities are the player's own bar skills?
-------------------------------------------------------------------------------
local function AbilityName(id) return zo_strformat(SI_ABILITY_NAME, GetAbilityName(id)) end

-- (skillType:line:skill) of the skill-tree skill an abilityId belongs to, any rank/morph; nil if it is not a skill
local function SkillKey(id)
    local st, sl, si = GetSpecificSkillAbilityKeysByAbilityId(id)
    if st and st > 0 and sl and sl > 0 and si and si > 0 then return st .. ":" .. sl .. ":" .. si end
end

-- Everything currently slotted on the player's bars (both weapon bars + werewolf/overload), scribed skills included.
local function Snapshot(s)
    s = s or { names = {}, icons = {}, keys = {} }
    local first, last = GetAssignableAbilityBarStartAndEndSlots()
    for c = 1, #HOTBARS do
        local cat = HOTBARS[c]
        for slot = first, last do
            local kind, id = GetSlotType(slot, cat), nil
            if kind == ACTION_TYPE_ABILITY then
                id = GetSlotBoundId(slot, cat)
            elseif kind == ACTION_TYPE_CRAFTED_ABILITY then
                id = GetAbilityIdForCraftedAbilityId(GetSlotBoundId(slot, cat))
            end
            if id and id > 0 then
                local nm = AbilityName(id)
                if nm ~= "" then s.names[nm] = true; s.icons[nm] = s.icons[nm] or GetAbilityIcon(id) end
                local key = SkillKey(id)
                if key then s.keys[key] = true end
            end
        end
    end
    return s
end

-------------------------------------------------------------------------------
-- Processing: runs once, after the session ends.
-------------------------------------------------------------------------------
local function AddSpan(spans, s, e, lo, hi)
    if s < lo then s = lo end
    if e > hi then e = hi end
    if e > s then spans[#spans + 1] = { s - lo, e - lo } end
end

-- union of possibly-overlapping { start, end } spans -> flat { s1, e1, s2, e2, ... }, total covered ms
local function Union(spans)
    table.sort(spans, function(x, y) return x[1] < y[1] end)
    local flat, total, cs, ce = {}, 0, nil, nil
    for i = 1, #spans do
        local sp = spans[i]
        if cs and sp[1] <= ce then
            if sp[2] > ce then ce = sp[2] end
        else
            if cs then flat[#flat + 1] = cs; flat[#flat + 1] = ce; total = total + ce - cs end
            cs, ce = sp[1], sp[2]
        end
    end
    if cs then flat[#flat + 1] = cs; flat[#flat + 1] = ce; total = total + ce - cs end
    return flat, total
end

local function ByPct(a, b)
    if a.pct ~= b.pct then return a.pct > b.pct end
    return a.name < b.name
end

local function Build(lo, hi, snap)
    -- 1) replay raw events into per-ability, per-target spans
    local per = {}
    for i = 1, n, STRIDE do
        local t, id, unit, change, endT = buf[i], buf[i + 1], buf[i + 2], buf[i + 3], buf[i + 4]
        local a = per[id]
        if not a then a = { live = {}, spans = {} }; per[id] = a end
        local u = a.live[unit]
        if change == EFFECT_RESULT_FADED then
            if u then AddSpan(a.spans, u[1], t, lo, hi); a.live[unit] = nil end
        else
            -- a fade event was missed (target died / out of range): close at its known expiry
            if u and t > u[2] then AddSpan(a.spans, u[1], u[2], lo, hi); u = nil end
            local expire = endT > 0 and endT * 1000 or math.huge
            if u then u[2] = expire else a.live[unit] = { t, expire } end
        end
    end

    -- 2) group every abilityId that shares a name: multi-step skills (e.g. Deep Fissure) log several ids but are ONE spell
    local groups = {}
    for id, a in pairs(per) do
        for _, u in pairs(a.live) do AddSpan(a.spans, u[1], math.min(u[2], hi), lo, hi) end
        if #a.spans > 0 then
            local name = AbilityName(id)
            if name ~= "" then
                local g = groups[name]
                if not g then g = { spans = {}, best = -1 }; groups[name] = g end
                local raw = 0
                for _, sp in ipairs(a.spans) do g.spans[#g.spans + 1] = sp; raw = raw + sp[2] - sp[1] end
                if raw > g.best then g.best, g.icon = raw, GetAbilityIcon(id) end
                if not g.active then
                    local key = SkillKey(id)
                    g.active = snap.names[name] or (key and snap.keys[key]) or false
                end
            end
        end
    end

    -- 3) union spans per group, split into actives (on the bars) and passives (everything else)
    local duration, actives, passives = hi - lo, {}, {}
    for name, g in pairs(groups) do
        local flat, total = Union(g.spans)
        local row = { name = name, icon = (g.active and snap.icons[name]) or g.icon, pct = total / duration, spans = flat }
        local list = g.active and actives or passives
        list[#list + 1] = row
    end
    table.sort(actives, ByPct)
    table.sort(passives, ByPct)
    return { duration = duration, actives = actives, passives = passives, time = startTime, zone = zoneName, boss = bossName }
end

-------------------------------------------------------------------------------
-- Encounter history
-------------------------------------------------------------------------------
local Populate -- forward declaration (UI section)

local function Trim()
    local over = #encounters - sv.maxEncounters
    if over > 0 then
        for _ = 1, over do table.remove(encounters, 1) end
        selected = zo_max(1, selected - over)
    end
end

local function AddEncounter(e)
    local followLatest = selected == #encounters      -- viewing the newest (or nothing yet): keep following
    encounters[#encounters + 1] = e
    if followLatest then selected = #encounters end
    Trim()
end

local function RefreshIfOpen(resetScroll)
    if UptimeGraphsWindow and not UptimeGraphsWindow:IsHidden() then Populate(resetScroll) end
end

-------------------------------------------------------------------------------
-- Logging control. Effect/boss events are only registered while logging.
-------------------------------------------------------------------------------
local function SafeSnapshot(into)
    local ok, s = pcall(Snapshot, into)
    if ok then return s end
    if not UG.snapshotWarned then
        UG.snapshotWarned = true
        Say("|cffcc66could not read your action bars (" .. tostring(s) .. "); everything will be listed as passive.|r")
    end
    return into or { names = {}, icons = {}, keys = {} }
end

local function StartLogging(isManual)
    if logging then return end
    logging, manual = true, isManual
    n, startMs, combatEndMs, bossName = 0, GetTimeMs(), nil, nil
    startTime = GetTimeString()
    zoneName = zo_strformat("<<1>>", GetPlayerLocationName())

    EM:RegisterForEvent(NAME .. "_FX", EVENT_EFFECT_CHANGED, OnEffect)
    EM:AddFilterForEvent(NAME .. "_FX", EVENT_EFFECT_CHANGED,
        REGISTER_FILTER_SOURCE_COMBAT_UNIT_TYPE, COMBAT_UNIT_TYPE_PLAYER)
    EM:RegisterForEvent(NAME .. "_Boss", EVENT_BOSSES_CHANGED, OnBossesChanged)

    -- buffs already running on the player when logging starts don't fire a gain event
    for i = 1, GetNumBuffs("player") do
        local _, _, timeEnding, _, _, _, _, _, _, _, abilityId, _, castByPlayer = GetUnitBuffInfo("player", i)
        if castByPlayer then
            buf[n + 1], buf[n + 2], buf[n + 3] = startMs, abilityId, 0
            buf[n + 4], buf[n + 5] = EFFECT_RESULT_GAINED, timeEnding
            n = n + STRIDE
        end
    end
    slotted = SafeSnapshot()
end

local function StopLogging()
    if not logging then return end
    logging, manual = false, false
    EM:UnregisterForUpdate(NAME .. "_End")
    EM:UnregisterForEvent(NAME .. "_FX", EVENT_EFFECT_CHANGED)
    EM:UnregisterForEvent(NAME .. "_Boss", EVENT_BOSSES_CHANGED)
    OnBossesChanged()                                   -- last chance to label the fight

    local hi = combatEndMs or GetTimeMs()
    local ok = hi - startMs >= MIN_FIGHT_MS
    if ok then
        local built, enc = pcall(Build, startMs, hi, SafeSnapshot(slotted))
        if built then
            AddEncounter(enc)
            RefreshIfOpen(false)
        else
            ok = false
            Say("|cff6666failed to process the fight:|r " .. tostring(enc))
        end
    end
    n = 0
    return ok
end

local function OnCombatState(_, inCombat)
    if manual then return end
    if inCombat then
        EM:UnregisterForUpdate(NAME .. "_End")
        combatEndMs = nil
        StartLogging(false)
    elseif logging then
        combatEndMs = GetTimeMs()
        EM:RegisterForUpdate(NAME .. "_End", END_DELAY_MS, function()
            EM:UnregisterForUpdate(NAME .. "_End")
            if not IsUnitInCombat("player") then StopLogging() else combatEndMs = nil end
        end)
    end
end

-------------------------------------------------------------------------------
-- UI
-------------------------------------------------------------------------------
local function Clock(ms)
    local s = zo_floor(ms / 1000)
    return string.format("%d:%02d", zo_floor(s / 60), s % 60)
end

-- Draws one row's timeline: X axis = encounter time, filled = ability was up.
-- Insets follow ZOS convention (see dyeing_shared.xml): left/top positive, right/bottom NEGATIVE = inward.
local function DrawBar(row, bar, spans, dur, col)
    local useComp = sv.useComposite
    local comp, segs = row.comp, row.segs
    if not comp then comp = bar:GetNamedChild("Graph"); row.comp = comp end
    if useComp then
        comp:SetHidden(false)
        comp:ClearAllSurfaces()
        if segs then for j = 1, #segs do segs[j]:SetHidden(true) end end
    else
        comp:SetHidden(true)
        if not segs then segs = {}; row.segs = segs end
    end

    local px, k, i, count = dur / barW, 0, 1, #spans
    while i <= count do
        local s, e = spans[i], spans[i + 1]
        i = i + 2
        while i <= count and spans[i] - e < px do e = spans[i + 1]; i = i + 2 end   -- merge sub-pixel gaps
        k = k + 1
        local x1 = zo_floor(s * barW / dur)
        local x2 = zo_max(x1 + 1, zo_ceil(e * barW / dur))
        if useComp then
            local idx = comp:AddSurface(TC_L, TC_R, TC_T, TC_B)
            comp:SetInsets(idx, x1, x2 - barW, 0, 0)
            comp:SetColor(idx, col[1], col[2], col[3], 1)
        else
            local seg = segs[k]
            if not seg then
                seg = CreateControl(nil, bar, CT_TEXTURE)
                seg:SetDrawLevel(1)
                segs[k] = seg
            end
            seg:SetColor(col[1], col[2], col[3], 1)       -- rows are recycled between green and blue lines
            seg:ClearAnchors()
            seg:SetAnchor(TOPLEFT, bar, TOPLEFT, x1, 0)
            seg:SetDimensions(x2 - x1, BAR_H)
            seg:SetHidden(false)
        end
    end
    if not useComp then for j = k + 1, #segs do segs[j]:SetHidden(true) end end
end

local function SetupRow(row, d)
    local isPrev = d.isPrev
    local icon, nameL, pctL = row:GetNamedChild("Icon"), row:GetNamedChild("Name"), row:GetNamedChild("Pct")
    local txt = isPrev and TXT_PREV or TXT_CUR
    nameL:SetColor(txt[1], txt[2], txt[3], 1)
    pctL:SetColor(txt[1], txt[2], txt[3], 1)
    if isPrev then                                   -- the "previous parse" line under a row
        icon:SetHidden(true)
        nameL:SetText(string.format("  previous  (%s)", Clock(d.dur)))
        pctL:SetText(d.pct and string.format("%.1f%%", d.pct * 100) or "n/a")
    else
        icon:SetHidden(false)
        icon:SetTexture(d.icon)
        nameL:SetText(d.name)
        pctL:SetText(string.format("%.1f%%", d.pct * 100))
    end
    local bar = row:GetNamedChild("Bar")
    bar:SetWidth(barW)
    DrawBar(row, bar, d.spans, d.dur or viewed.duration, isPrev and COL_PREV or COL_CUR)
end

-------------------------------------------------------------------------------
-- Comparison (current parse vs the one before it); rows are matched by ability name
-------------------------------------------------------------------------------
local function IndexByName(e)
    local m = {}
    for i = 1, #e.actives do m[e.actives[i].name] = e.actives[i] end
    for i = 1, #e.passives do m[e.passives[i].name] = e.passives[i] end
    return m
end

-- [row1, prev1, row2, prev2, ...]: every ability gets a second line with the previous parse's graph
local function Interleave(rows, prevIdx, prev)
    local out = {}
    for i = 1, #rows do
        local r, p = rows[i], prevIdx[rows[i].name]
        out[#out + 1] = r
        out[#out + 1] = { isPrev = true, name = r.name, pct = p and p.pct, spans = p and p.spans or EMPTY, dur = prev.duration }
    end
    return out
end

local function ByChange(a, b)
    local x, y = math.abs(a.delta), math.abs(b.delta)
    if x ~= y then return x > y end
    return a.name < b.name
end

-- change in uptime, in percentage points (80% now vs 72% before = +8.0%); biggest change first.
-- Abilities that existed before but not now are included (they are the "worse" ones you would otherwise never see).
local function Diff(cur, prev)
    local pIdx, cIdx = IndexByName(prev), IndexByName(cur)
    local A, P = {}, {}
    local function add(list, name, c, p)
        list[#list + 1] = { name = name, cur = c and c.pct, prev = p and p.pct, delta = (c and c.pct or 0) - (p and p.pct or 0) }
    end
    for i = 1, #cur.actives  do local r = cur.actives[i];  add(A, r.name, r, pIdx[r.name]) end
    for i = 1, #cur.passives do local r = cur.passives[i]; add(P, r.name, r, pIdx[r.name]) end
    for i = 1, #prev.actives  do local r = prev.actives[i];  if not cIdx[r.name] then add(A, r.name, nil, r) end end
    for i = 1, #prev.passives do local r = prev.passives[i]; if not cIdx[r.name] then add(P, r.name, nil, r) end end
    table.sort(A, ByChange)
    table.sort(P, ByChange)
    return { actives = A, passives = P }
end

local function SetupDeltaRow(row, d)
    row:GetNamedChild("Name"):SetText(d.name)
    row:GetNamedChild("Mid"):SetText(string.format("%s -> %s",
        d.prev and string.format("%.1f", d.prev * 100) or "n/a", d.cur and string.format("%.1f", d.cur * 100) or "n/a"))
    local delta = row:GetNamedChild("Delta")
    local col, text = DELTA_FLAT, "0.0%"
    if d.delta > DELTA_EPS then col, text = DELTA_UP, string.format("%+.1f%%", d.delta * 100)
    elseif d.delta < -DELTA_EPS then col, text = DELTA_DOWN, string.format("%+.1f%%", d.delta * 100) end
    delta:SetText(text)
    delta:SetColor(col[1], col[2], col[3], 1)
end

-- Splits the available height: actives get what they need (up to half, more if the passives are short).
local function Split(availH, nA, nP, rowH)
    local want, pwant = zo_max(nA, 1) * rowH, zo_max(nP, 1) * rowH
    local aH = zo_min(want, zo_max(zo_floor(availH / 2), availH - pwant))
    return zo_max(rowH, zo_min(aH, availH - rowH))
end

-- Panel sits on the window's right edge; flips to the left edge only when the screen has no room on the right.
local function AnchorPanel()
    local win, panel = UptimeGraphsWindow, UptimeGraphsCompare
    panel:ClearAnchors()
    if win:GetRight() + PANEL_GAP + PANEL_W <= GuiRoot:GetWidth() then
        panel:SetAnchor(TOPLEFT, win, TOPRIGHT, PANEL_GAP, 0)
        panel:SetAnchor(BOTTOMLEFT, win, BOTTOMRIGHT, PANEL_GAP, 0)
    else
        panel:SetAnchor(TOPRIGHT, win, TOPLEFT, -PANEL_GAP, 0)
        panel:SetAnchor(BOTTOMRIGHT, win, BOTTOMLEFT, -PANEL_GAP, 0)
    end
    panel:SetWidth(PANEL_W)
end

local function UpdateCompare(cur, prev, resetScroll)
    local panel = UptimeGraphsCompare
    if not sv.compare or UptimeGraphsWindow:IsHidden() then panel:SetHidden(true); return end
    panel:SetHidden(false)
    AnchorPanel()

    local diff = cur and prev and Diff(cur, prev) or nil
    local aL, pL = UptimeGraphsCompareActives, UptimeGraphsComparePassives
    local parts = { UptimeGraphsCompareActivesLabel, aL, UptimeGraphsCompareDivider, UptimeGraphsComparePassivesLabel, pL }
    for i = 1, #parts do parts[i]:SetHidden(diff == nil) end
    UptimeGraphsCompareMsg:SetHidden(diff ~= nil)

    if not diff then
        UptimeGraphsCompareSub:SetText("")
        UptimeGraphsCompareMsg:SetText(cur and "No earlier parse to compare with. Use the < arrow to pick a later parse." or "Nothing to compare yet.")
        return
    end
    UptimeGraphsCompareSub:SetText(string.format("previous #%d (%s, %.1fs)   ->   now #%d", selected - 1, prev.time or "", prev.duration / 1000, selected))
    UptimeGraphsCompareActivesLabel:SetText(string.format("ACTIVES (%d)", #diff.actives))
    UptimeGraphsComparePassivesLabel:SetText(string.format("PASSIVES (%d)", #diff.passives))

    local _, H = UptimeGraphsWindow:GetDimensions()
    local availH = zo_max(PROW_H * 2, H - P_LIST_TOP - P_SECTION_GAP - P_PAD)
    local aH = Split(availH, #diff.actives, #diff.passives, PROW_H)
    UptimeGraphsCompareActivesLabel:ClearAnchors()
    UptimeGraphsCompareActivesLabel:SetAnchor(TOPLEFT, panel, TOPLEFT, P_PAD + 4, P_LIST_TOP - 20)
    aL:ClearAnchors()
    aL:SetAnchor(TOPLEFT, panel, TOPLEFT, P_PAD, P_LIST_TOP)
    aL:SetAnchor(TOPRIGHT, panel, TOPRIGHT, -P_PAD, P_LIST_TOP)
    ZO_ScrollList_SetHeight(aL, aH)
    local y = P_LIST_TOP + aH + 6
    UptimeGraphsCompareDivider:ClearAnchors()
    UptimeGraphsCompareDivider:SetAnchor(TOPLEFT, panel, TOPLEFT, P_PAD, y)
    UptimeGraphsCompareDivider:SetAnchor(TOPRIGHT, panel, TOPRIGHT, -P_PAD, y)
    y = y + 7
    UptimeGraphsComparePassivesLabel:ClearAnchors()
    UptimeGraphsComparePassivesLabel:SetAnchor(TOPLEFT, panel, TOPLEFT, P_PAD + 4, y)
    y = y + 20
    pL:ClearAnchors()
    pL:SetAnchor(TOPLEFT, panel, TOPLEFT, P_PAD, y)
    pL:SetAnchor(TOPRIGHT, panel, TOPRIGHT, -P_PAD, y)
    ZO_ScrollList_SetHeight(pL, zo_max(PROW_H, H - y - P_PAD))

    local sets = { { aL, diff.actives }, { pL, diff.passives } }
    for i = 1, 2 do
        local list, rows = sets[i][1], sets[i][2]
        ZO_ScrollList_Clear(list)
        local data = ZO_ScrollList_GetDataList(list)
        for r = 1, #rows do data[r] = ZO_ScrollList_CreateDataEntry(ROW_TYPE, rows[r]) end
        ZO_ScrollList_Commit(list)
        if resetScroll then ZO_ScrollList_ResetToTop(list) end
    end
end

-- Sizes everything from the window size: bar width, time axis, the two tables and their divider.
local function Layout(nA, nP)
    local win = UptimeGraphsWindow
    local W, H = win:GetDimensions()
    barW = zo_max(60, W - PAD * 2 - ZO_SCROLL_BAR_WIDTH - ROW_LEFT - ROW_RIGHT)

    local barLeft = PAD + ROW_LEFT
    local axisStart, axisMid, axisEnd = UptimeGraphsWindowAxisStart, UptimeGraphsWindowAxisMid, UptimeGraphsWindowAxisEnd
    axisStart:ClearAnchors(); axisStart:SetAnchor(TOPLEFT, win, TOPLEFT, barLeft, AXIS_Y)
    axisMid:ClearAnchors();   axisMid:SetAnchor(TOP, win, TOPLEFT, barLeft + zo_floor(barW / 2), AXIS_Y)
    axisEnd:ClearAnchors();   axisEnd:SetAnchor(TOPRIGHT, win, TOPLEFT, barLeft + barW, AXIS_Y)
    UptimeGraphsWindowInfo:SetWidth(zo_max(40, W - INFO_LEFT - COMPARE_W - 28))
    local check = UptimeGraphsWindowCompareCheck
    check:ClearAnchors()
    check:SetAnchor(TOPLEFT, win, TOPRIGHT, -(COMPARE_W + 14), 47)

    local availH = zo_max(ROW_H * 2, H - LIST_TOP - SECTION_GAP - PAD)
    local activesH = Split(availH, nA, nP, ROW_H)

    UptimeGraphsWindowActivesLabel:ClearAnchors()
    UptimeGraphsWindowActivesLabel:SetAnchor(TOPLEFT, win, TOPLEFT, PAD + 4, LABEL_Y)
    local actives = UptimeGraphsWindowActives
    actives:ClearAnchors()
    actives:SetAnchor(TOPLEFT, win, TOPLEFT, PAD, LIST_TOP)
    actives:SetAnchor(TOPRIGHT, win, TOPRIGHT, -PAD, LIST_TOP)
    ZO_ScrollList_SetHeight(actives, activesH)

    local y = LIST_TOP + activesH + 6
    local divider = UptimeGraphsWindowDivider
    divider:ClearAnchors()
    divider:SetAnchor(TOPLEFT, win, TOPLEFT, PAD, y)
    divider:SetAnchor(TOPRIGHT, win, TOPRIGHT, -PAD, y)
    y = y + 7
    UptimeGraphsWindowPassivesLabel:ClearAnchors()
    UptimeGraphsWindowPassivesLabel:SetAnchor(TOPLEFT, win, TOPLEFT, PAD + 4, y)
    y = y + 20
    local passives = UptimeGraphsWindowPassives
    passives:ClearAnchors()
    passives:SetAnchor(TOPLEFT, win, TOPLEFT, PAD, y)
    passives:SetAnchor(TOPRIGHT, win, TOPRIGHT, -PAD, y)
    ZO_ScrollList_SetHeight(passives, zo_max(ROW_H, H - y - PAD))   -- explicit, so Commit never reads a stale height
end

local function UpdateHeader()
    local e = viewed
    UptimeGraphsWindowNavCount:SetText(string.format("%d / %d", selected, #encounters))
    UptimeGraphsWindowNavPrev:SetEnabled(selected > 1)
    UptimeGraphsWindowNavNext:SetEnabled(selected < #encounters)
    if e then
        UptimeGraphsWindowInfo:SetText(string.format("%s  |  %.1fs  |  %s", e.time or "", e.duration / 1000, e.boss or e.zone or ""))
        UptimeGraphsWindowAxisStart:SetText("0:00")
        UptimeGraphsWindowAxisMid:SetText(Clock(e.duration / 2))
        UptimeGraphsWindowAxisEnd:SetText(Clock(e.duration))
        UptimeGraphsWindowActivesLabel:SetText(string.format("ACTIVES (%d)  -  skills on your bars", #e.actives))
        UptimeGraphsWindowPassivesLabel:SetText(string.format("PASSIVES (%d)  -  buffs, debuffs, sets and passive effects", #e.passives))
    else
        UptimeGraphsWindowInfo:SetText("No encounter recorded yet")
        UptimeGraphsWindowAxisStart:SetText("")
        UptimeGraphsWindowAxisMid:SetText("")
        UptimeGraphsWindowAxisEnd:SetText("")
        UptimeGraphsWindowActivesLabel:SetText("ACTIVES  -  skills on your bars")
        UptimeGraphsWindowPassivesLabel:SetText("PASSIVES  -  buffs, debuffs, sets and passive effects")
    end
end

Populate = function(resetScroll)
    viewed = encounters[selected]
    if viewed ~= shown then resetScroll, shown = true, viewed end
    local prev = (sv.compare and viewed and selected > 1) and encounters[selected - 1] or nil

    local aRows, pRows = viewed and viewed.actives or EMPTY, viewed and viewed.passives or EMPTY
    if prev then                                    -- compare ON: a blue "previous parse" line under every row
        local idx = IndexByName(prev)
        aRows, pRows = Interleave(aRows, idx, prev), Interleave(pRows, idx, prev)
    end

    Layout(#aRows, #pRows)
    UpdateHeader()
    local sets = { { UptimeGraphsWindowActives, aRows }, { UptimeGraphsWindowPassives, pRows } }
    for i = 1, 2 do
        local list, rows = sets[i][1], sets[i][2]
        ZO_ScrollList_Clear(list)
        local data = ZO_ScrollList_GetDataList(list)
        for r = 1, #rows do data[r] = ZO_ScrollList_CreateDataEntry(ROW_TYPE, rows[r]) end
        ZO_ScrollList_Commit(list)
        if resetScroll then ZO_ScrollList_ResetToTop(list) end
    end
    UpdateCompare(viewed, prev, resetScroll)
end

local function Toggle()
    local w = UptimeGraphsWindow
    local wasHidden = w:IsHidden()
    SCENE_MANAGER:ToggleTopLevel(w)
    if w:IsHidden() == wasHidden then   -- scene manager refused (window not registered): never fail silently
        Say("|cff6666Scene manager did not toggle the window; forcing it.|r")
        w:SetHidden(not wasHidden)
        if wasHidden then SCENE_MANAGER:SetInUIMode(true) end
    end
end

UG.Toggle       = Guard(Toggle)
UG.OnShow       = Guard(function() Populate(false) end)
UG.OnResizeStop = Guard(function()
    sv.w, sv.h = UptimeGraphsWindow:GetDimensions()
    Populate(false)
end)
UG.OnMoveStop   = Guard(function()
    sv.x, sv.y = UptimeGraphsWindow:GetLeft(), UptimeGraphsWindow:GetTop()
    if sv.compare then AnchorPanel() end             -- may need to flip sides near the screen edge
end)
UG.OnHide       = Guard(function() UptimeGraphsCompare:SetHidden(true) end)
UG.NavPrev      = Guard(function() if selected > 1 then selected = selected - 1; Populate(true) end end)
UG.NavNext      = Guard(function() if selected < #encounters then selected = selected + 1; Populate(true) end end)

-------------------------------------------------------------------------------
-- Commands, settings, init
-------------------------------------------------------------------------------
function UG.ToggleLogging()
    if logging then
        local wasManual = manual
        if StopLogging() then
            local e = encounters[#encounters]
            Say(string.format("Logging |cff6666STOPPED|r%s: %.1fs, %d actives / %d passives. Use /uptimes to view.",
                wasManual and "" or " (auto session ended early)", e.duration / 1000, #e.actives, #e.passives))
        else
            Say(string.format("Logging |cff6666STOPPED|r, but the session was under %ds so it was discarded.", MIN_FIGHT_MS / 1000))
        end
    else
        StartLogging(true)
        Say("Logging |c66ff66STARTED|r (manual: ignores combat state). Run /uptimelog again to stop.")
    end
end

local function RegisterMenu()
    local LAM = LibAddonMenu2
    if not LAM then return end
    local id = NAME .. "Options"
    LAM:RegisterAddonPanel(id, {
        type = "panel", name = "Uptime Graphs", displayName = "Uptime Graphs", version = VERSION,
        registerForRefresh = true, registerForDefaults = true,
    })
    LAM:RegisterOptionControls(id, {
        {
            type = "slider", name = "Encounters to keep",
            tooltip = "How many finished combat encounters stay browsable in the window. The oldest are dropped first.",
            min = 1, max = 100, step = 1, default = DEFAULTS.maxEncounters,
            getFunc = function() return sv.maxEncounters end,
            setFunc = function(v) sv.maxEncounters = v; Trim(); RefreshIfOpen(false) end,
        },
        {
            type = "checkbox", name = "Draw bars with TextureComposite",
            tooltip = "Fast path: one control per bar. Turn this off if the bars ever fail to appear; it falls back to plain textures.",
            default = DEFAULTS.useComposite,
            getFunc = function() return sv.useComposite end,
            setFunc = function(v)
                sv.useComposite = v
                ZO_ScrollList_RefreshVisible(UptimeGraphsWindowActives)
                ZO_ScrollList_RefreshVisible(UptimeGraphsWindowPassives)
            end,
        },
    })
end

local function Init()
    sv = ZO_SavedVars:NewAccountWide("UptimeGraphs_SV", 1, nil, DEFAULTS)
    UG.sv = sv
    local win = UptimeGraphsWindow
    win:SetDimensions(sv.w, sv.h)
    if sv.x then
        win:ClearAnchors()
        win:SetAnchor(TOPLEFT, GuiRoot, TOPLEFT, sv.x, sv.y)
    end
    -- Without this, SCENE_MANAGER:ToggleTopLevel() silently does nothing. false = Esc / leaving cursor mode closes it.
    SCENE_MANAGER:RegisterTopLevel(win, false)
    ZO_ScrollList_AddDataType(UptimeGraphsWindowActives, ROW_TYPE, "UG_Row", ROW_H, SetupRow)
    ZO_ScrollList_AddDataType(UptimeGraphsWindowPassives, ROW_TYPE, "UG_Row", ROW_H, SetupRow)
    ZO_ScrollList_AddDataType(UptimeGraphsCompareActives, ROW_TYPE, "UG_DeltaRow", PROW_H, SetupDeltaRow)
    ZO_ScrollList_AddDataType(UptimeGraphsComparePassives, ROW_TYPE, "UG_DeltaRow", PROW_H, SetupDeltaRow)

    local check = UptimeGraphsWindowCompareCheck
    ZO_CheckButton_SetLabelText(check, "Compare with previous parse")
    ZO_CheckButton_SetTooltipText(check, "Shows the previous parse's uptime (blue) under every row, and lists how much each uptime changed in a panel on the right.")
    ZO_CheckButton_SetToggleFunction(check, Guard(function(_, checked) sv.compare = checked; Populate(true) end))
    ZO_CheckButton_SetCheckState(check, sv.compare)
    EM:RegisterForEvent(NAME, EVENT_PLAYER_COMBAT_STATE, OnCombatState)
end

local function OnLoaded(_, name)
    if name ~= NAME then return end
    EM:UnregisterForEvent(NAME, EVENT_ADD_ON_LOADED)

    local ok, err = pcall(Init)
    if not ok then UG.initError = tostring(err) end
    if ok then
        local menuOk, menuErr = pcall(RegisterMenu)
        if not menuOk then UG.menuError = tostring(menuErr) end
    end

    SLASH_COMMANDS["/uptimes"]   = UG.Toggle
    SLASH_COMMANDS["/uptimelog"] = Guard(UG.ToggleLogging)
end

EM:RegisterForEvent(NAME, EVENT_ADD_ON_LOADED, OnLoaded)
