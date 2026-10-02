module

public import C4Check

public section

/-! Cells `3193 ≤ n < 3195` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir092

theorem k3193_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3193) 3).1
      1).isSome = true := by
  decide +kernel

theorem k3193_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3193) 3).2 3).1
      553869583798263016549770508541898999472210974).isSome = true := by
  decide +kernel

theorem k3193_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3193) 3).2 3).2 2).1
      23051695207352898619903351444435898264611612490802424382986445089179024088840025523209593180346765070253292289065514670523849).isSome = true := by
  decide +kernel

theorem k3193_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3193) 3).2 3).2 2).2
      66189360802389073008542934451597552850618698055137914671444681470162702874122277446).isSome = true := by
  decide +kernel

theorem k3194_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).1
      1979190964539693371011145041433433826464726614973141930992092259953298365565204628557565110872660218181207431107578155460800899744759549957282070802657322977856447942).isSome = true := by
  decide +kernel

theorem k3194_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).2 2).1
      89774560157542605313744159636474206943931609956935564443272720168924058814065917994971936622685350456516553997792599137940721).isSome = true := by
  decide +kernel

theorem k3194_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).2 2).2
      16115212547839151343886674561314580455452106045026071810020758858618588490256092529).isSome = true := by
  decide +kernel

theorem k3194_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).2 3).1
      260958285990335341974087244514766985929392169428745159830683017112209130929487671110).isSome = true := by
  decide +kernel

theorem k3194_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).2 3).2
      6635281284412262192831325409366147583835777043159248617448138916458338600444582079429285563672356517120783763902885022201304992016944513494832582).isSome = true := by
  decide +kernel

theorem k3194_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).1 2).1
      1205849279947839901686594498732124416231005856687523490585534782450146764641881809082483457943394156271420).isSome = true := by
  decide +kernel

theorem k3194_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).1 2).2
      5566254366701346394377690330442065274367267478267791881787888723623328270521613000604713756694809589478645652039606738605884).isSome = true := by
  decide +kernel

theorem k3194_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).2 2).1
      64852464093536441908935659416700645966383741472953377820027276537202132618593217008444).isSome = true := by
  decide +kernel

theorem k3194_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).2 2).2
      64922907658457104410263954708119112337956005885573884720305295239324089479415522120508).isSome = true := by
  decide +kernel

theorem k3194_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).1
      26318096338085614331590038646190825501093467527714942303458702630082789785570330741844338662533863126245502009810923495214178862176726016767034822).isSome = true := by
  decide +kernel

theorem k3194_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).2 2).1
      299516422580887741737549730680887893734057442363097980208692266650581404868124216881094651152729100687217).isSome = true := by
  decide +kernel

theorem k3194_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).2 2).2
      15868403957038658442306288879484176893491890909459324161013662423775844981501697393).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3193 3195 :=
  (Cover.one (box := dirCellBox) (n := 3193)
      (.split 3 (.leaf _ k3193_0) (.split 3 (.leaf _ k3193_1) (.split 2 (.leaf _ k3193_2) (.leaf _ k3193_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3194)
      (.split 3 (.split 2 (.split 3 (.leaf _ k3194_0) (.split 2 (.leaf _ k3194_1) (.leaf _ k3194_2))) (.split 3 (.leaf _ k3194_3) (.leaf _ k3194_4))) (.split 2 (.split 3 (.split 2 (.leaf _ k3194_5) (.leaf _ k3194_6)) (.split 2 (.leaf _ k3194_7) (.leaf _ k3194_8))) (.split 3 (.leaf _ k3194_9) (.split 2 (.leaf _ k3194_10) (.leaf _ k3194_11))))))

end C4.Cert.Dir092
