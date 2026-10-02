module

public import C4Check

public section

/-! Cells `3558 ≤ n < 3559` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir113

theorem k3558_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).1
      425144890460454400517102909429103930702352799902759871200873372366995464815004671253969288941091768679643849320093687934359565920307532449621434161).isSome = true := by
  decide +kernel

theorem k3558_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).1 3).2
      104883235899084569490516954288228330717030139445483606815721213834782362975673588477469455692254495179744756567360093769874661430900652018841255089).isSome = true := by
  decide +kernel

theorem k3558_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).2 3).1
      360784923570178014768684809782485855858257498224876548068752114900762133713611766840493017493927139608278667934614526279245617).isSome = true := by
  decide +kernel

theorem k3558_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).1 2).2 3).2
      1425750258732515149481411166085633049244450498179269642365485317279504134333653100026539282400176249238790975806696038470213425).isSome = true := by
  decide +kernel

theorem k3558_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).1 2).1
      16597734377763506100858852074107513177649826967551195942599266534537247589213103742129).isSome = true := by
  decide +kernel

theorem k3558_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).1 2).2
      265926717601066693216029824112490561949414638873966462822314225610385122291861642659013).isSome = true := by
  decide +kernel

theorem k3558_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).2 2).1
      4100436493921737921941946861304248880248642507778641417438198640507360348438098171697).isSome = true := by
  decide +kernel

theorem k3558_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).1 2).2 3).2 2).2
      4107166663052302816029583025879231908210849484235039825282050118550926949300108629809).isSome = true := by
  decide +kernel

theorem k3558_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).1 3).1
      22526843925293851326585713523422874740241084317139127000496890959304199057586452991767435624985911683811216218061352597892747977).isSome = true := by
  decide +kernel

theorem k3558_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).1 3).2
      74053445630027647383471812312711359265681443513519372697217828150738584068456013914738091021061253651889).isSome = true := by
  decide +kernel

theorem k3558_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).1
      1037924866427756852003054458901948370658103558437906338170057416983299133464659909633841).isSome = true := by
  decide +kernel

theorem k3558_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).1 2).2 3).2
      1186597244311973271994163350829303955512643758561697937388165207347894406523572973492882671598908818218161).isSome = true := by
  decide +kernel

theorem k3558_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).1 3).1
      4061286224215095719460983135605144539711620028317253985496571320081326561337302013745).isSome = true := by
  decide +kernel

theorem k3558_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).1 3).2
      16119587930455648481390602296615511616466880246316369603205940625674436596880599111473).isSome = true := by
  decide +kernel

theorem k3558_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).2 3).1
      4068570883667203963766532390558893312172961848910766592298800712945047229113651418929).isSome = true := by
  decide +kernel

theorem k3558_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3558) 3).2 2).2 2).2 3).2
      4037244480985833242789580497613792842254899426754196255328572092820994022622423471921).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3558 3559 :=
  (Cover.one (box := dirCellBox) (n := 3558)
      (.split 3 (.split 2 (.split 2 (.split 3 (.leaf _ k3558_0) (.leaf _ k3558_1)) (.split 3 (.leaf _ k3558_2) (.leaf _ k3558_3))) (.split 3 (.split 2 (.leaf _ k3558_4) (.leaf _ k3558_5)) (.split 2 (.leaf _ k3558_6) (.leaf _ k3558_7)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3558_8) (.leaf _ k3558_9)) (.split 3 (.leaf _ k3558_10) (.leaf _ k3558_11))) (.split 2 (.split 3 (.leaf _ k3558_12) (.leaf _ k3558_13)) (.split 3 (.leaf _ k3558_14) (.leaf _ k3558_15))))))

end C4.Cert.Dir113
