module

public import C4Check

public section

/-! Cells `3563 ≤ n < 3587` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir110

theorem k3563_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3563) 2).1
      169791069032239771209113529405931214561926823005356312013908391446086435166).isSome = true := by
  decide +kernel

theorem k3563_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3563) 2).2 2).1
      21218217443106066544429884577620028398700132876292945161601565861866052391332397925667565861117954268293065284666225613358535).isSome = true := by
  decide +kernel

theorem k3563_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3563) 2).2 2).2 3).1
      4496062539947052973086792906822382043017405387541999749751047627264977640398556940564121240090647549425).isSome = true := by
  decide +kernel

theorem k3563_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3563) 2).2 2).2 3).2
      15224539634746618547899052966422922402312898831217367575390822527545056189021946225).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 3564 3585 [
    4936791273100777190758135024884049741487495021468941197290660087928074146893030041767503737803185139868842417315862,
    5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3585_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3585) 3).1
      1).isSome = true := by
  decide +kernel

theorem k3585_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3585) 3).2 3).1
      49281840587254457867543867992037641506009126978276499255808582477172014075991909593518174).isSome = true := by
  decide +kernel

theorem k3585_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3585) 3).2 3).2 2).1 1).1
      19434549421062721459797100052802399044316659333035065978795933520422872891497231945832074256413993629518).isSome = true := by
  decide +kernel

theorem k3585_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3585) 3).2 3).2 2).1 1).2
      19382738527358485848283454126432910618150329613360617938570975707037262906364280644907274211225468801870).isSome = true := by
  decide +kernel

theorem k3585_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3585) 3).2 3).2 2).2
      263614646980161728205311948926408952484010427645435508664375760246378493397850066249).isSome = true := by
  decide +kernel

theorem k3586_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).1 3).1 1).1
      78474435891497784176984676764255476004544792167326999232673226982778914707596750179649300101177327576896714).isSome = true := by
  decide +kernel

theorem k3586_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).1 3).1 1).2
      1256257112408854536278892983032993461285404970789826679563742968158319667177787924405540440003295535200819082).isSome = true := by
  decide +kernel

theorem k3586_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).1 3).2 2).1
      6741678516376324922261409995442680359842581113589855298547282588672585766478903944795955430882257458429353362285212272003105110865236368892589079729).isSome = true := by
  decide +kernel

theorem k3586_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).1 3).2 2).2
      310228791511190162925502921216254190897201801916766243794977879922171149830211931812469736024307825404632241).isSome = true := by
  decide +kernel

theorem k3586_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).2 3).1
      1974341704938025580651685814579672669900511516459678338313267165271616265302931498652802197212214966521025139199518068402368797414443245824274428110146421833839773129).isSome = true := by
  decide +kernel

theorem k3586_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).2 3).2 1).1
      65744270824972497506992883591519610738512653203002313422642899466116176445861810082502).isSome = true := by
  decide +kernel

theorem k3586_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).2 3).2 1).2
      55633552724023576191866625500474268588539434526748576188706461490).isSome = true := by
  decide +kernel

theorem k3586_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).1 3).1 1).1
      16289168159056998821691825220815104347001420476102730761239530349511113484858986355506).isSome = true := by
  decide +kernel

theorem k3586_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).1 3).1 1).2
      4064171080994559742697855843633602560570716754075379418381902848208746427478118930226).isSome = true := by
  decide +kernel

theorem k3586_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).1 3).2 1).1
      1193394286140300315944176808843279084884451286226067103483391029672684961349793132681491105738960190403532).isSome = true := by
  decide +kernel

theorem k3586_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).1 3).2 1).2
      64652917009773080632237562160418604270536699736148212929697096444747377188434708683570).isSome = true := by
  decide +kernel

theorem k3586_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).2 3).1
      1674749206797395469767921990014360872771312985793228923246971329407194003333037015326176806610349981636487297736537786337988098844432723685236236081).isSome = true := by
  decide +kernel

theorem k3586_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).2 3).2
      106411879360934281660750753121190004373045778342042718042915731188902383467362288037263291426180176472802149609664452689418566961172572581625519886129).isSome = true := by
  decide +kernel

theorem k3586_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).2 3).1 1).1
      16354234636052480024517277963314876438207292266534216118477233518527433569854026962738).isSome = true := by
  decide +kernel

theorem k3586_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).2 3).1 1).2
      4817509335610698945727571169402184378842839847095110199653372975493668423787202897523012137339486882618162).isSome = true := by
  decide +kernel

theorem k3586_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).2 3).2 1).1
      4778080999255874088753702845308749676087709308460501547810995762326675648425443384468048593991133559152434).isSome = true := by
  decide +kernel

theorem k3586_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).2 3).2 1).2
      5651837026803563727534318993104933820776098062053376435889483272876926390632798519830439550215044992368398788528322258823142194).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3563 3587 :=
  (Cover.one (box := dirCellBox) (n := 3563)
      (.split 2 (.leaf _ k3563_0) (.split 2 (.leaf _ k3563_1) (.split 3 (.leaf _ k3563_2) (.leaf _ k3563_3))))).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 3585)
      (.split 3 (.leaf _ k3585_0) (.split 3 (.leaf _ k3585_1) (.split 2 (.split 1 (.leaf _ k3585_2) (.leaf _ k3585_3)) (.leaf _ k3585_4))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3586)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3586_0) (.leaf _ k3586_1)) (.split 2 (.leaf _ k3586_2) (.leaf _ k3586_3))) (.split 3 (.leaf _ k3586_4) (.split 1 (.leaf _ k3586_5) (.leaf _ k3586_6)))) (.split 2 (.split 2 (.split 3 (.split 1 (.leaf _ k3586_7) (.leaf _ k3586_8)) (.split 1 (.leaf _ k3586_9) (.leaf _ k3586_10))) (.split 3 (.leaf _ k3586_11) (.leaf _ k3586_12))) (.split 3 (.split 1 (.leaf _ k3586_13) (.leaf _ k3586_14)) (.split 1 (.leaf _ k3586_15) (.leaf _ k3586_16))))))

end C4.Cert.Dir110
