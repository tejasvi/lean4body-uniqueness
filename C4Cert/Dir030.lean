module

public import C4Check

public section

/-! Cells `2083 ≤ n < 2109` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir030

theorem k2083_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2083) 3).1
      248928945258501038383026865478375045779442017842064111230343334882933783928945216601148).isSome = true := by
  decide +kernel

theorem k2083_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2083) 3).2
      995425668586142910527552079282408770620801256521760437754925744349735631507729986712369).isSome = true := by
  decide +kernel

theorem k2084_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2084) 2).1
      3887483642533608757017078958958469683481275841815231805333330659448368368548619310897).isSome = true := by
  decide +kernel

theorem k2084_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2084) 2).2
      971876242949972062613916922373489328117876113064129719650850217196278979205527338044).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 2085 2103 [
    971339699497997252132746915544581425405060966069452826478342552068990176351774920007,
    147532564051065897412, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c3 : allCells dirCell 2103 2104 [
    6600183906357321123447407390456979116465560228236016719716066444679481997697018537693608133362744319950295496045257067718106470058625823070988628047] = true := by
  decide +kernel

theorem k2104_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2104) 3).1
      21693163158054167622673300272315236007159104920601294116718263541233024581500085672487084963813833624387961866461646544283206).isSome = true := by
  decide +kernel

theorem k2104_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2104) 3).2 2).1
      1349105948199066138769117455917685794778623154069182950058393509351972659624751902407610905479805447630513042954975796147569).isSome = true := by
  decide +kernel

theorem k2104_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2104) 3).2 2).2
      3872232127349908466063039438763898372204455108686421625086515780966325629066763644).isSome = true := by
  decide +kernel

theorem k2105_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2105) 3).1 2).1
      72843032673525913620268233959576886523244852425521680438936855219888362633404971965038798878383672068465).isSome = true := by
  decide +kernel

theorem k2105_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2105) 3).1 2).2
      18217517657889497366919817311465760676914553109156775147075983005866296474228788777988398171237111395580).isSome = true := by
  decide +kernel

theorem k2105_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2105) 3).2 2).1
      5359776196152105333246153853798976408567151330117118645538321567531922149801923631499157190126711515425520203976147662788412).isSome = true := by
  decide +kernel

theorem k2105_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2105) 3).2 2).2
      4649532164514164996879916774305011488084266211679209690138275183997585888502669424317891618277852727570684).isSome = true := by
  decide +kernel

theorem k2106_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2106) 3).1 2).1
      289820593365254875176438178138484018062631417386644119475677716289165408567090479613594986006323385586492).isSome = true := by
  decide +kernel

theorem k2106_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2106) 3).1 2).2
      251421555362923144500915382052667716161858712409193001624853416297683874062182842846012).isSome = true := by
  decide +kernel

theorem k2106_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2106) 3).2 2).1
      62711122753019349695333635037501696578381996557744278366224489851398228826272288416572).isSome = true := by
  decide +kernel

theorem k2106_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2106) 3).2 2).2
      62722895363700022035601140914294229658399697267025148557744150568513893627049497535292).isSome = true := by
  decide +kernel

theorem k2107_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2107) 3).1 2).1
      978442199899881026602541421713234688697981313298658388161068969782738730050572352572).isSome = true := by
  decide +kernel

theorem k2107_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2107) 3).1 2).2
      15657579520761275109171481959093095427369667733179142345833309982268417180796297134908).isSome = true := by
  decide +kernel

theorem k2107_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2107) 3).2 2).1
      211836602576453391551543105742619918602806705070407754717355883580).isSome = true := by
  decide +kernel

theorem k2107_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2107) 3).2 2).2
      211872576940809971210467734046503296933296419774623353012995013692).isSome = true := by
  decide +kernel

theorem k2108_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2108) 3).1
      22290979880650910159889031418371982791187934789463361636755046103848244169590310949980728868203023088214760235739088833599845495026).isSome = true := by
  decide +kernel

theorem k2108_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2108) 3).2
      1392081912393165022092229272735589058826941753365109902286301701187311351254529009635996186993648369544165387601763755170012286770).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2083 2109 :=
  (Cover.one (box := dirCellBox) (n := 2083)
      (.split 3 (.leaf _ k2083_0) (.leaf _ k2083_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2084)
      (.split 2 (.leaf _ k2084_0) (.leaf _ k2084_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 2104)
      (.split 3 (.leaf _ k2104_0) (.split 2 (.leaf _ k2104_1) (.leaf _ k2104_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2105)
      (.split 3 (.split 2 (.leaf _ k2105_0) (.leaf _ k2105_1)) (.split 2 (.leaf _ k2105_2) (.leaf _ k2105_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2106)
      (.split 3 (.split 2 (.leaf _ k2106_0) (.leaf _ k2106_1)) (.split 2 (.leaf _ k2106_2) (.leaf _ k2106_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2107)
      (.split 3 (.split 2 (.leaf _ k2107_0) (.leaf _ k2107_1)) (.split 2 (.leaf _ k2107_2) (.leaf _ k2107_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2108)
      (.split 3 (.leaf _ k2108_0) (.leaf _ k2108_1)))

end C4.Cert.Dir030
