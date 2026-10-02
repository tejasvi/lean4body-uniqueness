module

public import C4Check

public section

/-! Cells `3714 ≤ n < 3738` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir127

theorem c0 : allCells dirCell 3714 3728 [
    147559797236305877780, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    3994113270214634209434600971250779028751144869309430553951703133181875477002869109255] = true := by
  decide +kernel

theorem k3728_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3728) 3).1
      86548760621876424402340536564534879553971037170198780216281344721668803976640298069261982094217276715608393347075377439274226).isSome = true := by
  decide +kernel

theorem k3728_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3728) 3).2
      253402681008309108250584872265072366322084677455810842006328450904480133358751031062770).isSome = true := by
  decide +kernel

theorem k3729_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3729) 2).1
      351586210928027657337331468965717810462992105953028959557497567443652262410004693205877960577432237092928077155077183157906657073).isSome = true := by
  decide +kernel

theorem k3729_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3729) 2).2
      18591857229250360239314632249514196042727661587314528055587257113669534975830672735193231372056232071288627).isSome = true := by
  decide +kernel

theorem k3730_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3730) 2).1
      87450235452617323803819679066375323246663106919660000169526945198008356488886760104528212513199431514787430684888765769333559091).isSome = true := by
  decide +kernel

theorem k3730_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3730) 2).2
      16077270804778050060503559876229147116884389749574178960754011770760346789454708689026108).isSome = true := by
  decide +kernel

theorem k3731_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3731) 2).1
      87216474780829106448934196516352948912826835202661924672576068100091530936686729992380661696320124577275223363125558536606011187).isSome = true := by
  decide +kernel

theorem k3731_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3731) 2).2
      16030367961063744831987564445161116272303563774117869692528272906031993878252269950155836).isSome = true := by
  decide +kernel

theorem k3732_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3732) 2).1
      15993877986832487105814540122884871540335728373608286694459750676467059492440212210138172).isSome = true := by
  decide +kernel

theorem k3732_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3732) 2).2
      15997029510316518343539104543306815104692603253428809055065706564178614829670458218200124).isSome = true := by
  decide +kernel

theorem k3733_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3733) 3).1
      15976478789602627661379746015554908728875174148648097736100513118869863611560544709590076).isSome = true := by
  decide +kernel

theorem k3733_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3733) 3).2
      3991552562697401267851351312654256130957211506838657997402839752900556446784026110016572).isSome = true := by
  decide +kernel

theorem k3734_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3734) 1).1
      15954940845915236227040381021195314921864867341592999342086857068859063401244917322808380).isSome = true := by
  decide +kernel

theorem k3734_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3734) 1).2
      3988671414669404435043700467602174654325250007787918452503399225506365265767967047334972).isSome = true := by
  decide +kernel

theorem k3735_0 : (checkBoxH dirMode depth (dirCellBox 3735)
      36565795045305730266165772449291921511678201266388194031914179883813303809078584937299240063993589534331139773807782360136787365004248072083220309166440522954623977365666553084937705388850004796).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 3736 3737 [
    347024233184298688931131640821289277745224458555415921095541233418464649904494525616167905572243166057709744455131157616525296444] = true := by
  decide +kernel

theorem c10 : allCells dirCell 3737 3738 [
    75215931405399853185479763882905436444815330592308681621121548000318142283913583067579167531140208010470605628] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3714 3738 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 3728)
      (.split 3 (.leaf _ k3728_0) (.leaf _ k3728_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3729)
      (.split 2 (.leaf _ k3729_0) (.leaf _ k3729_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3730)
      (.split 2 (.leaf _ k3730_0) (.leaf _ k3730_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3731)
      (.split 2 (.leaf _ k3731_0) (.leaf _ k3731_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3732)
      (.split 2 (.leaf _ k3732_0) (.leaf _ k3732_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3733)
      (.split 3 (.leaf _ k3733_0) (.leaf _ k3733_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3734)
      (.split 1 (.leaf _ k3734_0) (.leaf _ k3734_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3735)
      (.leaf _ k3735_0)).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10)

end C4.Cert.Dir127
