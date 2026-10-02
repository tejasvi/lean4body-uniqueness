module

public import C4Check

public section

/-! Cells `4122 ≤ n < 4149` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir141

theorem k4122_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4122) 2).1
      256903362226578405014753679474879188145254297233051043382682327398938005693988442272639795).isSome = true := by
  decide +kernel

theorem k4122_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4122) 2).2
      16071345125158897490861113718233521582014308549521497971990894448344784892512359067011889).isSome = true := by
  decide +kernel

theorem k4123_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4123) 2).1
      18907957497887150285313177508819576636657271445793887316658520430815212895544015955270328050870667692717412147).isSome = true := by
  decide +kernel

theorem k4123_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4123) 2).2
      250413702292012057462635156210979266700868293006240707627443256275045586396311205983180).isSome = true := by
  decide +kernel

theorem k4124_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4124) 3).1
      16000325268130852894665893664933876664357025460459592858111827844345389883185040521903164).isSome = true := by
  decide +kernel

theorem k4124_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4124) 3).2
      15986502805166645403271088787868733868880686772151059680597973107295530154020956454206524).isSome = true := by
  decide +kernel

theorem k4125_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4125) 2).1
      73645669464990725314275081745461301940980826034982397404051435795590333740479622066483361403245233857936444).isSome = true := by
  decide +kernel

theorem k4125_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4125) 2).2
      998192181984353014845085549346922044887567935769300360611098458094282819596591155067964).isSome = true := by
  decide +kernel

theorem k4126_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4126) 2).1
      844526765238549204323305495338125232800327428281009640399011232828).isSome = true := by
  decide +kernel

theorem k4126_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4126) 2).2
      18395153661919297194672924208853339941845745144381920900869782578902284630777384884912035499669178323254332).isSome = true := by
  decide +kernel

theorem k4127_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4127) 3).1
      973280743097891850905366628027399328121960834309185458250147809172965447148983123004).isSome = true := by
  decide +kernel

theorem k4127_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4127) 3).2
      972968571696122412256588458424146272316690061096938645787656370262947390437063490620).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4128 4129 [
    1203979815783453357071152060427480954527561612691835435280428157679997034746922328626451052769138881832524170044] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4129 4130 [
    1387593148697281196963130585180831396349309972536783837713988338080308416375070402841120082900730619256303724557875236564732199740] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4130 4131 [
    15550917673950817190370879348849689653320689776727700132419938945828042959498767745852] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4131 4132 [
    15547656664763832785015998572761934663207224317562009270347179352582308266268958376764] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4132 4133 [
    15545156749742491182055404970951335068315863607650350772628665229421672935464398996284] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4133 4147 [
    52662400144698385266471030629931740427754098631612979203203215612,
    43556741996673032969441975585292188807260, 147562421495729619268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] = true := by
  decide +kernel

theorem c12 : allCells dirCell 4147 4148 [
    2861138015332516639926980687252079053739299] = true := by
  decide +kernel

theorem k4148_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4148) 3).1
      15508348144581162926080154194905220774095110179118805622019174474780147316815650162).isSome = true := by
  decide +kernel

theorem k4148_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4148) 3).2
      3956273502809916680547045336930497460356127801824049455270764174548285150996170200882).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4122 4149 :=
  (Cover.one (box := dirCellBox) (n := 4122)
      (.split 2 (.leaf _ k4122_0) (.leaf _ k4122_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4123)
      (.split 2 (.leaf _ k4123_0) (.leaf _ k4123_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4124)
      (.split 3 (.leaf _ k4124_0) (.leaf _ k4124_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4125)
      (.split 2 (.leaf _ k4125_0) (.leaf _ k4125_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4126)
      (.split 2 (.leaf _ k4126_0) (.leaf _ k4126_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4127)
      (.split 3 (.leaf _ k4127_0) (.leaf _ k4127_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.one (box := dirCellBox) (n := 4148)
      (.split 3 (.leaf _ k4148_0) (.leaf _ k4148_1)))

end C4.Cert.Dir141
