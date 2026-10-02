module

public import C4Check

public section

/-! Cells `1239 ≤ n < 1269` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir007

theorem k1239_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1239) 3).1 2).1
      3903441227152016626129873234680621306105570911039780801580911238858799624712680582477).isSome = true := by
  decide +kernel

theorem k1239_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1239) 3).1 2).2
      3904960976618005106870268945625469063026757214285526560798146023989169658490269582669).isSome = true := by
  decide +kernel

theorem k1239_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1239) 3).2 2).1
      1151220374473756974796732554784400554015841092471172019502973660390693114810425819645223637053451212511025).isSome = true := by
  decide +kernel

theorem k1239_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1239) 3).2 2).2
      3901653985306026993217710260348928208837487876242429766002405877306146172869399254833).isSome = true := by
  decide +kernel

theorem k1240_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1240) 3).1 2).1
      62334124842178142305502195838640078093044264727237922499083799704072889467569392817969).isSome = true := by
  decide +kernel

theorem k1240_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1240) 3).1 2).2
      62347458156600590945766042949947748382108920789699295710064834060123055492122831673137).isSome = true := by
  decide +kernel

theorem k1240_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1240) 3).2 2).1
      3893725013434476599144216619663309552024765477960925463367892356914351514775247516364).isSome = true := by
  decide +kernel

theorem k1240_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1240) 3).2 2).2
      3377946644895940132997072530861099647804146036375814696044995253041).isSome = true := by
  decide +kernel

theorem k1241_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1241) 2).1
      308144477756977359080633918623292391646499866734040117426746251126487904278859509316525905821996583596942658227399).isSome = true := by
  decide +kernel

theorem k1241_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1241) 2).2 3).1
      973163308203868580249974476848559156325312293903054518451840599512753213468013591756).isSome = true := by
  decide +kernel

theorem k1241_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1241) 2).2 3).2
      3373941888512869995749838739933600441495045589138225341013685269297).isSome = true := by
  decide +kernel

theorem k1242_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1242) 2).1
      16305105171095863890142531911322274106893952555571563173426188746604099956200818948858924231).isSome = true := by
  decide +kernel

theorem k1242_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1242) 2).2
      3980516789188495447320391088523713917886301386697206793836233467075213226057773792719667).isSome = true := by
  decide +kernel

theorem k1243_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1243) 2).1
      15542981616971423448406410227144787068292182005887631595930841454058298306727992233351).isSome = true := by
  decide +kernel

theorem k1243_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1243) 2).2
      242861371266862705840954142118165101707920117826193750387227753990125526596478277427).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 1244 1266 [
    174137572292056311757723547218174383012690, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 51] = true := by
  decide +kernel

theorem k1266_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1266) 3).1
      3920854745345914555999939807170428562973183591867153322121808915942358501390485444358).isSome = true := by
  decide +kernel

theorem k1266_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1266) 3).2
      5456976080826132363232412302921961715868683485736876090129281991076678373236608330730504433568844008784403283411181301566959942).isSome = true := by
  decide +kernel

theorem k1267_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1267) 3).1 2).1
      244149875218150913838707293938016546621324583622197177008132960336659416371071367537).isSome = true := by
  decide +kernel

theorem k1267_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1267) 3).1 2).2
      244230180537675727820101913975240574252173052890001359755193345024825940525071439217).isSome = true := by
  decide +kernel

theorem k1267_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1267) 3).2 2).1
      975701679769738260585225467161556762399466716631915338357363442811136670672579558460).isSome = true := by
  decide +kernel

theorem k1267_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1267) 3).2 2).2
      975934587416466050642382142461407233142770491341405151793839211413960305818579336252).isSome = true := by
  decide +kernel

theorem k1268_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1268) 3).1
      22261120560919641308068382733318886029777902113087837169043215357402770718752373620856359189878222708119424688452909673106422783174).isSome = true := by
  decide +kernel

theorem k1268_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1268) 3).2
      308587125571025142028862672304404498703846671968933215680227174020732100470030144392025933966434149776761127652553).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1239 1269 :=
  (Cover.one (box := dirCellBox) (n := 1239)
      (.split 3 (.split 2 (.leaf _ k1239_0) (.leaf _ k1239_1)) (.split 2 (.leaf _ k1239_2) (.leaf _ k1239_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1240)
      (.split 3 (.split 2 (.leaf _ k1240_0) (.leaf _ k1240_1)) (.split 2 (.leaf _ k1240_2) (.leaf _ k1240_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1241)
      (.split 2 (.leaf _ k1241_0) (.split 3 (.leaf _ k1241_1) (.leaf _ k1241_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1242)
      (.split 2 (.leaf _ k1242_0) (.leaf _ k1242_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1243)
      (.split 2 (.leaf _ k1243_0) (.leaf _ k1243_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 1266)
      (.split 3 (.leaf _ k1266_0) (.leaf _ k1266_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1267)
      (.split 3 (.split 2 (.leaf _ k1267_0) (.leaf _ k1267_1)) (.split 2 (.leaf _ k1267_2) (.leaf _ k1267_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1268)
      (.split 3 (.leaf _ k1268_0) (.leaf _ k1268_1)))

end C4.Cert.Dir007
