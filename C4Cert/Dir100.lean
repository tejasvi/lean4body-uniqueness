module

public import C4Check

public section

/-! Cells `3255 ≤ n < 3279` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir100

theorem k3255_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3255) 2).1 3).1
      1181481961204805360068659668690845605453602776058938931095791880270710583008374772351212103967609272768865084).isSome = true := by
  decide +kernel

theorem k3255_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3255) 2).1 3).2
      1180144088834703144466187747276910906493564633201216288658909356414496357116608499074768670000653894338683708).isSome = true := by
  decide +kernel

theorem k3255_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3255) 2).2 3).1
      256295112762069057768264932487465675924410989526168012012442156243047028558515442470077244).isSome = true := by
  decide +kernel

theorem k3255_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3255) 2).2 3).2
      63993536592216061953733682878777218023387362055777057183244710766867073012689813665465148).isSome = true := by
  decide +kernel

theorem k3256_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3256) 3).1 2).1
      3383591127774491134498057381792870600946507814814976638839993344828).isSome = true := by
  decide +kernel

theorem k3256_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3256) 3).1 2).2
      846201664285371509705947353788604963677668769924892234333124281148).isSome = true := by
  decide +kernel

theorem k3256_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3256) 3).2 2).1
      13524668027239368440203679690217189997957835919685339799882672579388).isSome = true := by
  decide +kernel

theorem k3256_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3256) 3).2 2).2
      845546809962270910888095509750799985333200105636182863228844884796).isSome = true := by
  decide +kernel

theorem k3257_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3257) 3).1 1).1
      211245317835654251694316187017529964919561675716658768223047351356).isSome = true := by
  decide +kernel

theorem k3257_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3257) 3).1 1).2
      3379593404884291184403252987645362097498225585444457131409984176956).isSome = true := by
  decide +kernel

theorem k3257_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3257) 3).2
      25635959306484379421978861689887679929465357285262687103921806798012548971612579463958941077949407351963823984399480973106312864026137758324980917052).isSome = true := by
  decide +kernel

theorem k3258_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3258) 3).1
      5556671071496230624680195738026926149182638873985091898236834677019420158702274242086652381360782814060489360596909795804387330290).isSome = true := by
  decide +kernel

theorem k3258_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3258) 3).2
      15940397396539280777306213499161420490084594804596754473908270652771623138347580003830002).isSome = true := by
  decide +kernel

theorem k3259_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3259) 2).1
      1148138613500884908213504317710726345490293474800462367852527614596457881318177280007126309824047360199484).isSome = true := by
  decide +kernel

theorem k3259_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3259) 2).2
      287069842960750530600593403858492602223501913785778578136041596071822147994133951597983472336140729045820).isSome = true := by
  decide +kernel

theorem k3260_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3260) 3).1
      15555658549437141685520475475485045864495323705193634659912639480060209505919655463484).isSome = true := by
  decide +kernel

theorem k3260_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3260) 3).2
      15552807798862311727811018930182327845340014225788220406061915011795116412845954963826).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 3261 3262 [
    338656868790677178249005420074053795032248630877500104292732802922630156837640788117789963367033809674746177357375820379026674] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3262 3263 [
    84640588090373157003927740099522190364755466247505112239636106088008904892555169748873988275052152594680440669613129229235443] = true := by
  decide +kernel

theorem c8 : allCells dirCell 3263 3278 [
    15179499854972166933090559268494404374697517142236246937449287527819459327517485426,
    51422585074087122160812870745903016978907275594565266970463890, 2360991878578110635585, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 3278 3279 [
    158126944475824074494515] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3255 3279 :=
  (Cover.one (box := dirCellBox) (n := 3255)
      (.split 2 (.split 3 (.leaf _ k3255_0) (.leaf _ k3255_1)) (.split 3 (.leaf _ k3255_2) (.leaf _ k3255_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3256)
      (.split 3 (.split 2 (.leaf _ k3256_0) (.leaf _ k3256_1)) (.split 2 (.leaf _ k3256_2) (.leaf _ k3256_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3257)
      (.split 3 (.split 1 (.leaf _ k3257_0) (.leaf _ k3257_1)) (.leaf _ k3257_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3258)
      (.split 3 (.leaf _ k3258_0) (.leaf _ k3258_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3259)
      (.split 2 (.leaf _ k3259_0) (.leaf _ k3259_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3260)
      (.split 3 (.leaf _ k3260_0) (.leaf _ k3260_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9)

end C4.Cert.Dir100
