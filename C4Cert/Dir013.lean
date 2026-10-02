module

public import C4Check

public section

/-! Cells `1602 ≤ n < 1630` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir013

theorem k1602_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1602) 2).1 3).1
      25734651105513248842166481501029033729176641273828018326401215839070130592896384180379091276559891843132707426737683039334317025317200661641363748301).isSome = true := by
  decide +kernel

theorem k1602_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1602) 2).1 3).2
      1047401761900386016590559484294038952252946699483568731223923643466701810578631018933497648013).isSome = true := by
  decide +kernel

theorem k1602_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1602) 2).2 3).1
      25736983128322630045766293708658322805808986746735241794030951399652895554312090201045261160306621424443981426719447377108797597002525103677905819079).isSome = true := by
  decide +kernel

theorem k1602_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1602) 2).2 3).2
      4722459508193321086981490264158407941472281170791730441482366203170530230773389431510931861132415756708136141).isSome = true := by
  decide +kernel

theorem k1603_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1603) 2).1 3).1
      4088207571289030412026229918319807336497841703176543419994780451449614336475726576159544205).isSome = true := by
  decide +kernel

theorem k1603_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1603) 2).1 3).2
      249443693894394286640341062370224654932016834327657353011635190222218937877008087688393).isSome = true := by
  decide +kernel

theorem k1603_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1603) 2).2 3).1
      1047031699991675189171264244438195563603801548420591905351314434008854379028390927291968539845).isSome = true := by
  decide +kernel

theorem k1603_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1603) 2).2 3).2
      1021663025624297490335248346197406873988746918953047645778338722446119429660372353781451569).isSome = true := by
  decide +kernel

theorem k1604_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1604) 2).1 3).1
      3895050552408528038671759090842280619598927022138060028434853104957479395776943707953).isSome = true := by
  decide +kernel

theorem k1604_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1604) 2).1 3).2
      243358687659580894318053113919247658613152404078676711119269657809690371396810659633).isSome = true := by
  decide +kernel

theorem k1604_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1604) 2).2 3).1
      3896243552884591992837438833426089481872926163225915618798710396872451221004050159409).isSome = true := by
  decide +kernel

theorem k1604_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1604) 2).2 3).2
      3893877792044960140168451047579869508117184271002773278108561063146134167975143397169).isSome = true := by
  decide +kernel

theorem k1605_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1605) 2).1
      6251181790507776223162177710370464323617174551472162026013859486051797608623689687861300706029590316604791912204193404045956878811895451306784199).isSome = true := by
  decide +kernel

theorem k1605_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1605) 2).2
      4702934515906700470183661718510224450985396699556798007101529220251763205217546364495002679433224016115031239).isSome = true := by
  decide +kernel

theorem k1606_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1606) 2).1
      823194378138509709967361253809906724028354373259634190229386055).isSome = true := by
  decide +kernel

theorem k1606_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1606) 2).2
      338708574307869275491130925927255140348963460736370883181700492123297687997134884511098666629237739416386663509518169854739655).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 1607 1628 [
    15547508986326702311980900107327448834792460990799781695373531828916178596756754221318,
    2787666971926319472016443543091983843230994, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 1628 1629 [
    18634611581446246495212331546373080679421452590825368630262536431540939467876250626191509317489442039592163] = true := by
  decide +kernel

theorem k1629_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1629) 3).1 2).1
      982516684695299897952795845432799523725294697035530450695067179632584899923743799559).isSome = true := by
  decide +kernel

theorem k1629_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1629) 3).1 2).2
      18142114645475251788345712517007263786387973165644887122178813600876480007980909637204646035232969008497).isSome = true := by
  decide +kernel

theorem k1629_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1629) 3).2 2).1
      4625719189916184708335897518984215341028844058120216384360419726271906039376569880659053513555502064132173).isSome = true := by
  decide +kernel

theorem k1629_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1629) 3).2 2).2
      4629524660154308115510748252130256847818612407330295568129731792324160503969774729258903386172916886939719).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1602 1630 :=
  (Cover.one (box := dirCellBox) (n := 1602)
      (.split 2 (.split 3 (.leaf _ k1602_0) (.leaf _ k1602_1)) (.split 3 (.leaf _ k1602_2) (.leaf _ k1602_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1603)
      (.split 2 (.split 3 (.leaf _ k1603_0) (.leaf _ k1603_1)) (.split 3 (.leaf _ k1603_2) (.leaf _ k1603_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1604)
      (.split 2 (.split 3 (.leaf _ k1604_0) (.leaf _ k1604_1)) (.split 3 (.leaf _ k1604_2) (.leaf _ k1604_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1605)
      (.split 2 (.leaf _ k1605_0) (.leaf _ k1605_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1606)
      (.split 2 (.leaf _ k1606_0) (.leaf _ k1606_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 1629)
      (.split 3 (.split 2 (.leaf _ k1629_0) (.leaf _ k1629_1)) (.split 2 (.leaf _ k1629_2) (.leaf _ k1629_3))))

end C4.Cert.Dir013
