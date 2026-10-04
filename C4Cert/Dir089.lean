module

public import C4Check

public section

/-! Cells `3196 ≤ n < 3197` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir089

theorem k3196_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).1 3).1 1).1
      858620039904510250506498416960211260684992147815857632756469972028).isSome = true := by
  decide +kernel

theorem k3196_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).1 3).1 1).2
      3432754697339041813561413913961840192535272531392471074832862002236).isSome = true := by
  decide +kernel

theorem k3196_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).1 3).2 1).1
      252787864961720642521490811489093470409043945665348042395503134197471657518330013020732).isSome = true := by
  decide +kernel

theorem k3196_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).1 3).2 1).2
      3423825885760159575602429691203319489408664182485524582584479576636).isSome = true := by
  decide +kernel

theorem k3196_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).2 3).1 1).1
      3438096714923778267701779923169982212476496488910705910719046335548).isSome = true := by
  decide +kernel

theorem k3196_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).2 3).1 1).2
      3436049157292789337691860244263555279832871616709206872758590553148).isSome = true := by
  decide +kernel

theorem k3196_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).2 3).2 1).1
      857171645365230568424210793557958170116853650177666970281473588284).isSome = true := by
  decide +kernel

theorem k3196_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).1 2).2 3).2 1).2
      3427152903471230571798459276306307244187042076753849570500462623804).isSome = true := by
  decide +kernel

theorem k3196_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).1 3).1 1).1
      3418023026905569129465815357967578586206777062041198017002790711868).isSome = true := by
  decide +kernel

theorem k3196_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).1 3).1 1).2
      2896580927003147666889827764940144936640442940).isSome = true := by
  decide +kernel

theorem k3196_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).1 3).2 1).1
      852915973216254801664160186937524218999567023541998383360573436476).isSome = true := by
  decide +kernel

theorem k3196_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).1 3).2 1).2
      11553645541610893892489388491134891013118085692).isSome = true := by
  decide +kernel

theorem k3196_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).2 3).1
      19520947034503828636199262785771556495327887548570504734300346622841309768204919775057880339796205250271866450161).isSome = true := by
  decide +kernel

theorem k3196_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).2 3).2 1).1
      3414396693448248474273493599444487416956327403820339076632644416060).isSome = true := by
  decide +kernel

theorem k3196_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).1 3).2 2).2 3).2 1).2
      2890826195233876224412808735940652108695859772).isSome = true := by
  decide +kernel

theorem k3196_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).1 3).1 1).1
      860312260223307731640983197595920359076743024899100980481619770428).isSome = true := by
  decide +kernel

theorem k3196_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).1 3).1 1).2
      3362469151065044339144283747013637686979487354431468339066199756).isSome = true := by
  decide +kernel

theorem k3196_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).1 3).2 1).1
      3431754660878715279100716306768304720804326687802258919853106510908).isSome = true := by
  decide +kernel

theorem k3196_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).1 3).2 1).2
      214396661338595790334394470566718311770850737430268082254582885436).isSome = true := by
  decide +kernel

theorem k3196_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).2 3).1 1).1
      861018736254476242697692057874354568883118124055603250936833489980).isSome = true := by
  decide +kernel

theorem k3196_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).2 3).1 1).2
      3362009270610502276306798239653509118561328020683537921991925452).isSome = true := by
  decide +kernel

theorem k3196_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).2 3).2 1).1
      858604418553356316751475608798145372331745879628359617703644609596).isSome = true := by
  decide +kernel

theorem k3196_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).1 2).2 3).2 1).2
      3352642195049826321370494647150738213856316525860622551921090252).isSome = true := by
  decide +kernel

theorem k3196_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).1 3).1 1).1
      855897400774878515980501661989877535554715686789765455779953753148).isSome = true := by
  decide +kernel

theorem k3196_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).1 3).1 1).2
      3422222092546949257699575473876791640487656055036262851620623989820).isSome = true := by
  decide +kernel

theorem k3196_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).1 3).2
      19498197633598719703104328456972192111114032207800377687705738233351907287541245074666492468186923339085967192305).isSome = true := by
  decide +kernel

theorem k3196_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).2 3).1 1).1
      742823085442549618274075004173150372184838028348).isSome = true := by
  decide +kernel

theorem k3196_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).2 3).1 1).2
      53515203410322307906587275826502514273989548739620550623271185468).isSome = true := by
  decide +kernel

theorem k3196_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).2 3).2 1).1
      854769480133783890536589218041082414387609886142795920254149966908).isSome = true := by
  decide +kernel

theorem k3196_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3196) 2).2 3).2 2).2 3).2 1).2
      11580900372739171726294983845610487568583224380).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3196 3197 :=
  (Cover.one (box := dirCellBox) (n := 3196)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3196_0) (.leaf _ k3196_1)) (.split 1 (.leaf _ k3196_2) (.leaf _ k3196_3))) (.split 3 (.split 1 (.leaf _ k3196_4) (.leaf _ k3196_5)) (.split 1 (.leaf _ k3196_6) (.leaf _ k3196_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3196_8) (.leaf _ k3196_9)) (.split 1 (.leaf _ k3196_10) (.leaf _ k3196_11))) (.split 3 (.leaf _ k3196_12) (.split 1 (.leaf _ k3196_13) (.leaf _ k3196_14))))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3196_15) (.leaf _ k3196_16)) (.split 1 (.leaf _ k3196_17) (.leaf _ k3196_18))) (.split 3 (.split 1 (.leaf _ k3196_19) (.leaf _ k3196_20)) (.split 1 (.leaf _ k3196_21) (.leaf _ k3196_22)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3196_23) (.leaf _ k3196_24)) (.leaf _ k3196_25)) (.split 3 (.split 1 (.leaf _ k3196_26) (.leaf _ k3196_27)) (.split 1 (.leaf _ k3196_28) (.leaf _ k3196_29)))))))

end C4.Cert.Dir089
