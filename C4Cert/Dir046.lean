module

public import C4Check

public section

/-! Cells `2440 ≤ n < 2443` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir046

theorem k2440_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).1 3).1
      75177667889605807366859100981876432287149322470260364874791946499512171251856156504960634959989133255472369).isSome = true := by
  decide +kernel

theorem k2440_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).1 3).2
      74980234643448241335873833622781808923821672391863406617290120887268262015856592954061257092112558459252988).isSome = true := by
  decide +kernel

theorem k2440_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).2 1).1
      1172528777698306131019397427566142761327611311170675595806043731375327941232061752341497808604053905958387).isSome = true := by
  decide +kernel

theorem k2440_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).2 1).2
      15912558448746474915885822345910224925601303668069741226287366619208439118301885324476).isSome = true := by
  decide +kernel

theorem k2440_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).1 3).1
      253364838184575293419696219094329589552742301648261954807107686860794715040384292818748).isSome = true := by
  decide +kernel

theorem k2440_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).1 3).2
      15802101704344678333894127136297189646053507889619850688590936914665162107511255847740).isSome = true := by
  decide +kernel

theorem k2440_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).2 1).1
      15832826462196275636092578552111253622154109801558924360635797938522720206618443598652).isSome = true := by
  decide +kernel

theorem k2440_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).2 1).2
      858170251042839330958943156012853797337628022740422778064876327740).isSome = true := by
  decide +kernel

theorem k2441_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).1 3).1
      63094866855309316147458079626023316765416017611568113432806294691600957932743375180604).isSome = true := by
  decide +kernel

theorem k2441_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).1 3).2
      3413651243681335425212805750305960245406923109397321860343718726204).isSome = true := by
  decide +kernel

theorem k2441_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).2 1).1
      985895235973484281542011667892976973032860502434069977651552439843245676151412487740).isSome = true := by
  decide +kernel

theorem k2441_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).1 2).2 1).2
      213675624883957950729346728844256450331385411100439657670059215420).isSome = true := by
  decide +kernel

theorem k2441_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 2).1 1).1
      212959257611791522480835569357749757462879059763610082604144753724).isSome = true := by
  decide +kernel

theorem k2441_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 2).1 1).2
      851740663596711161935987780248261874758135178961186863771503131708).isSome = true := by
  decide +kernel

theorem k2441_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 2).2 1).1
      213096626392897733768951224112159963601439177339707972964650971708).isSome = true := by
  decide +kernel

theorem k2441_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2441) 3).2 2).2 1).2
      13317141452323271826115831617106226632251244486786775255690607676).isSome = true := by
  decide +kernel

theorem k2442_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2442) 3).1 2).1
      18946881820485279599115105927549135227823121398764836016891077887703594253535444905131651823042732622031048497).isSome = true := by
  decide +kernel

theorem k2442_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2442) 3).1 2).2
      349834444565228334644929680348018984683168640072870525718190842184435833297885373278300511461715839986647631934810273610103505724).isSome = true := by
  decide +kernel

theorem k2442_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2442) 3).2 2).1
      1182490645777294101698131031796235217016293049880951222842434404198085969379477206892423807467053336357551164).isSome = true := by
  decide +kernel

theorem k2442_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2442) 3).2 2).2
      1183036245082105470007403283474397046432973674654894504547721657252799275801660222438728342374479509054471228).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2440 2443 :=
  (Cover.one (box := dirCellBox) (n := 2440)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2440_0) (.leaf _ k2440_1)) (.split 1 (.leaf _ k2440_2) (.leaf _ k2440_3))) (.split 2 (.split 3 (.leaf _ k2440_4) (.leaf _ k2440_5)) (.split 1 (.leaf _ k2440_6) (.leaf _ k2440_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2441)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2441_0) (.leaf _ k2441_1)) (.split 1 (.leaf _ k2441_2) (.leaf _ k2441_3))) (.split 2 (.split 1 (.leaf _ k2441_4) (.leaf _ k2441_5)) (.split 1 (.leaf _ k2441_6) (.leaf _ k2441_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2442)
      (.split 3 (.split 2 (.leaf _ k2442_0) (.leaf _ k2442_1)) (.split 2 (.leaf _ k2442_2) (.leaf _ k2442_3))))

end C4.Cert.Dir046
