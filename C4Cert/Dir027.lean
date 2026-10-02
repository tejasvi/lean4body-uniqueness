module

public import C4Check

public section

/-! Cells `2048 ≤ n < 2052` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir027

theorem k2048_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2048) 3).1 2).1
      21615949627297010742366965804224234850065037605583470967974164919041909564565541269280568364902517651903432735922933742366535).isSome = true := by
  decide +kernel

theorem k2048_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2048) 3).1 2).2
      1354330207869217900513158858382083097572507953458041594005864834045305116880981776966242469423285859013652429654755674870129).isSome = true := by
  decide +kernel

theorem k2048_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).1 1).1
      3864212293669752622984809316280959254969997129265644776963506589368879390471052668).isSome = true := by
  decide +kernel

theorem k2048_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).1 1).2
      18222149812743069775893782279129493456571421278428522969170080401505536972190098183179209780588609695091).isSome = true := by
  decide +kernel

theorem k2048_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2048) 3).2 2).2
      1589336052331893418345046723828667532709612210370018309717942784763288749515870406163143520190256815029623042180227543024292046740026505151766343).isSome = true := by
  decide +kernel

theorem k2049_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).1 1).1
      15384942499273199077960092891697369727558319530418780207301228944909742459746617715).isSome = true := by
  decide +kernel

theorem k2049_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).1 1).2
      72699092812371378992962937699595512778668581552398022285240948512982614129137096527766412437135285417532).isSome = true := by
  decide +kernel

theorem k2049_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).2 1).1
      208783352484384614010387502241626423808866621251624546852166972).isSome = true := by
  decide +kernel

theorem k2049_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).2 1).2
      72753657535753760161221883745630776584089504611009150776720859401600089415713824775149779905189286114876).isSome = true := by
  decide +kernel

theorem k2049_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).1 1).1
      3928556771952021056463425218679727952462185549514463889949824266641650298766209970860).isSome = true := by
  decide +kernel

theorem k2049_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).1 1).2
      982155630489252075220263768866907273300105551223646650291738809374371901864916384828).isSome = true := by
  decide +kernel

theorem k2049_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2049) 3).2 2).2
      6468685792069924923678651920937662697906940431695090931443884926562074402765551102217082456780873283244231699876071717930577758457168670406162085105).isSome = true := by
  decide +kernel

theorem k2050_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).1 1).1
      980082093601714934146338943917376210834095094689980553450505050276496359681226013756).isSome = true := by
  decide +kernel

theorem k2050_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).1 1).2
      212437918811867731340442693214257458534330869397524569292511951932).isSome = true := by
  decide +kernel

theorem k2050_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2050) 3).1 2).2
      413124361526506791101969497754635107819176623966933551927724932406588463416449561460297483988620560894675323682156579279717888573001237966487333839676).isSome = true := by
  decide +kernel

theorem k2050_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2050) 3).2 2).1
      5453696956345245779113005251588555030437774404048351346009864684023053101958638903974088314168978924353763932255870321436252977).isSome = true := by
  decide +kernel

theorem k2050_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2050) 3).2 2).2
      87291413366707158280580631200031153464038970204472132344777207926474827825359273915668331467956260354467291399795939006966353713).isSome = true := by
  decide +kernel

theorem k2051_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2051) 3).1 2).1
      1361725047427371180210134905265380230537285674999929799840561999854789127928125643399977514859835172509864866393673302860577852).isSome = true := by
  decide +kernel

theorem k2051_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2051) 3).1 2).2
      1362220608666945400558877183957684796013994232044844325538400723396022836183304496922495833449556414150942795481946643886455868).isSome = true := by
  decide +kernel

theorem k2051_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2051) 3).2 2).1
      4608166148283766210410393977387847471302708648121229267737079306943424495958727515545104040962882010952652).isSome = true := by
  decide +kernel

theorem k2051_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2051) 3).2 2).2
      4609537223413983665201555183236378747660017421996273188757989377206622111931944522328423302973396860351436).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2048 2052 :=
  (Cover.one (box := dirCellBox) (n := 2048)
      (.split 3 (.split 2 (.leaf _ k2048_0) (.leaf _ k2048_1)) (.split 2 (.split 1 (.leaf _ k2048_2) (.leaf _ k2048_3)) (.leaf _ k2048_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2049)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2049_0) (.leaf _ k2049_1)) (.split 1 (.leaf _ k2049_2) (.leaf _ k2049_3))) (.split 2 (.split 1 (.leaf _ k2049_4) (.leaf _ k2049_5)) (.leaf _ k2049_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2050)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2050_0) (.leaf _ k2050_1)) (.leaf _ k2050_2)) (.split 2 (.leaf _ k2050_3) (.leaf _ k2050_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2051)
      (.split 3 (.split 2 (.leaf _ k2051_0) (.leaf _ k2051_1)) (.split 2 (.leaf _ k2051_2) (.leaf _ k2051_3))))

end C4.Cert.Dir027
