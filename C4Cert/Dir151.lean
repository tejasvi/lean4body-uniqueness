module

public import C4Check

public section

/-! Cells `4517 ≤ n < 4545` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir151

theorem c0 : allCells dirCell 4517 4518 [
    89033982444080557727714798780695481623580483336098618199934099964751368622779679611845601920323580974854380443401567257405504549106] = true := by
  decide +kernel

theorem k4518_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4518) 2).1
      973688150779201094426987829510112890789089839132362359773828989857987233447765965884).isSome = true := by
  decide +kernel

theorem k4518_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4518) 2).2
      211148295911115295317738489900366468905115852582030038318512913468).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 4519 4520 [
    88883376789553052391692923472499851104289464154987269171932804596522455384931601182577943859846676954071410949846563161151167775548] = true := by
  decide +kernel

theorem k4520_0 : (checkBoxH dirMode depth (dirCellBox 4520)
      102426197473986173533111977541352231982161749209355035017990226582469825213978244753100108111021405784842597804091459812538719618756770675462399341372).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 4521 4522 [
    4591318027235891577550660715697923613946871114827443363488231129754564252044931991406652536740830359925564] = true := by
  decide +kernel

theorem c5 : allCells dirCell 4522 4523 [
    248827624980826500268089853384166737270561145670690270995750993064003996184200047219516] = true := by
  decide +kernel

theorem c6 : allCells dirCell 4523 4524 [
    286819914989553533421725509337310252239234027969862899577390021967370301071018285030531730883772193166140] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4524 4525 [
    286774924294122702632529032448817410861595613792181522147298843952247365916973541109313830661842412229436] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4525 4526 [
    15544198266250532609814842470359672617579736482982936028967836554991716665724963205372] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4526 4539 [
    3291304709276086244654217817231332822102369151378780261053747452,
    12855644275095845117758062926006425026773284189417720054097276, 147564823035289068500, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4539 4540 [
    843868578586339472337616259658038548793373706790240117086639907] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4540 4541 [
    416458932198687204616373642854868264260394443502264417512955920036855863660762298517744125905645008380571360664602935447638917747046414928684136815819] = true := by
  decide +kernel

theorem k4541_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4541) 2).1
      13649995391378101182372413508929313970113464401265672768857325456179).isSome = true := by
  decide +kernel

theorem k4541_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4541) 2).2
      213279567815625414150063124061115690504513468478933897765177120563).isSome = true := by
  decide +kernel

theorem k4542_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4542) 2).1
      15693364009352332297654556826727061158414596774446659465595893277219135065123892741068).isSome = true := by
  decide +kernel

theorem k4542_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4542) 2).2
      850763555034878203606978227113981088872056170183685434062413036748).isSome = true := by
  decide +kernel

theorem k4543_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4543) 2).1
      15649650324561657454538986464677024681655855935316293207108794352661617102505438069708).isSome = true := by
  decide +kernel

theorem k4543_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4543) 2).2
      848438452996321816146030525831283331885936402232874532275536249804).isSome = true := by
  decide +kernel

theorem k4544_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4544) 2).1
      62474642566638462032181243779843248763538024383891017406784353870960481540996004258764).isSome = true := by
  decide +kernel

theorem k4544_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4544) 2).2
      15620809113217282847714488126988567066464961866143268191657889024670699939836624094156).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4517 4545 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 4518)
      (.split 2 (.leaf _ k4518_0) (.leaf _ k4518_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 4520)
      (.leaf _ k4520_0)).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.one (box := dirCellBox) (n := 4541)
      (.split 2 (.leaf _ k4541_0) (.leaf _ k4541_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4542)
      (.split 2 (.leaf _ k4542_0) (.leaf _ k4542_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4543)
      (.split 2 (.leaf _ k4543_0) (.leaf _ k4543_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4544)
      (.split 2 (.leaf _ k4544_0) (.leaf _ k4544_1)))

end C4.Cert.Dir151
