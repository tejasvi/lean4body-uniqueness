module

public import C4Check

public section

/-! Cells `2023 ≤ n < 2048` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir026

theorem k2023_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2023) 3).1 2).1
      75506052085706787095107673600904174061546967127415568251925165804851157241512690589618664535364690566386568397).isSome = true := by
  decide +kernel

theorem k2023_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2023) 3).1 2).2
      5443739987416521954879558735278819012247820362861019218815383792605827767305725168232824574318968941783011056039640587849554737).isSome = true := by
  decide +kernel

theorem k2023_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2023) 3).2 2).1
      84940055315311684243470589740805928963973176091921868634626907431473008165277101216629260108421153735570938626276519732671436).isSome = true := by
  decide +kernel

theorem k2023_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2023) 3).2 2).2
      4606053827979546460733341010588498581797152451369359435431664741593958787634734675451917235932188748100556).isSome = true := by
  decide +kernel

theorem k2024_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2024) 2).1 3).1
      3897262161427086403371051465135273604332122630904746223726378559500790962129639397169).isSome = true := by
  decide +kernel

theorem k2024_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2024) 2).1 3).2
      973832165827890432859631648699684269556075458658670945197605092795625235758635121724).isSome = true := by
  decide +kernel

theorem k2024_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2024) 2).2 3).1
      73634025908846563755254189871939674434315593477239852077968053763875795176625816657357767165634004703572940).isSome = true := by
  decide +kernel

theorem k2024_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2024) 2).2 3).2
      3299851867524270808491496274035806764697839599120896859532809164).isSome = true := by
  decide +kernel

theorem k2025_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2025) 2).1
      86774734498557135807975638906372065429880982464172560282116498636707849615992056786161732783183946695939568716882823473337826483).isSome = true := by
  decide +kernel

theorem k2025_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2025) 2).2
      347164485502716604052345954932357534660182597991203897394313013290497290129548634305789345294670969589822655550045235716696788787).isSome = true := by
  decide +kernel

theorem k2026_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2026) 2).1
      18367084622007250975468414721134878661850438805002510052702232970325422070497593224741009153433921222264007).isSome = true := by
  decide +kernel

theorem k2026_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2026) 2).2
      73468801091633222277085341629122783699357248218336122980537276680556351434985481430889989402567731713563847).isSome = true := by
  decide +kernel

theorem k2027_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2027) 2).1
      60748771478338195378647022951408967901546619400954256269368963013529470294817409869).isSome = true := by
  decide +kernel

theorem k2027_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2027) 2).2
      15549960131206799376170822830550219706899782085041657551362752132909047911561607173939).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2028 2029 [
    99933144423714049612268495057470490638186515916983768253850681424104354811178344824613151265109101386312424588944549091887791782115306502032913862] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2029 2047 [
    971377442741737042176440867292466200119703105438082907301411595265134288291216532038,
    2360627391567456065090, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k2047_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2047) 3).1
      13672504321854171094353519325919158581189199922229994007515748110).isSome = true := by
  decide +kernel

theorem k2047_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2047) 3).2
      1645239813972236389319494267752909064957818790682351275554068051634057171437062483525027760400135173325733869203791706300708400117003580075493561374).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2023 2048 :=
  (Cover.one (box := dirCellBox) (n := 2023)
      (.split 3 (.split 2 (.leaf _ k2023_0) (.leaf _ k2023_1)) (.split 2 (.leaf _ k2023_2) (.leaf _ k2023_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2024)
      (.split 2 (.split 3 (.leaf _ k2024_0) (.leaf _ k2024_1)) (.split 3 (.leaf _ k2024_2) (.leaf _ k2024_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2025)
      (.split 2 (.leaf _ k2025_0) (.leaf _ k2025_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2026)
      (.split 2 (.leaf _ k2026_0) (.leaf _ k2026_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2027)
      (.split 2 (.leaf _ k2027_0) (.leaf _ k2027_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2047)
      (.split 3 (.leaf _ k2047_0) (.leaf _ k2047_1)))

end C4.Cert.Dir026
