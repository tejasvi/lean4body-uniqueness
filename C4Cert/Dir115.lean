module

public import C4Check

public section

/-! Cells `3617 ≤ n < 3621` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir115

theorem k3617_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).1 2).1 1).1
      65918253667821143814672758772826255007816140808964880495501249336703346053939981650385629427).isSome = true := by
  decide +kernel

theorem k3617_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).1 2).1 1).2
      4021615294137453457859843278283240802432904858390068379822081681523755227002664033610931).isSome = true := by
  decide +kernel

theorem k3617_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).1 2).2 1).1
      16099254523893596351222915110228827030880405772961614930724321775443191198522556449921843).isSome = true := by
  decide +kernel

theorem k3617_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).1 2).2 1).2
      4027019131234508303737452200838935057308163993579385831147595781868989977539847810563132).isSome = true := by
  decide +kernel

theorem k3617_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).2 2).1 1).1
      1003943657498581124796093045560863981060627255105332097127392913419359307314596651987516).isSome = true := by
  decide +kernel

theorem k3617_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).2 2).1 1).2
      62688865429119783991883443013140161342611232747787633526592779778055087017583601999027).isSome = true := by
  decide +kernel

theorem k3617_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).2 2).2 1).1
      15708059472843651110339710923553646699892642519736980258849346791860847199203859741756).isSome = true := by
  decide +kernel

theorem k3617_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).2 2).2 1).2
      62755648806093720484594377957682510838533941885007544311165535156513945923350336827964).isSome = true := by
  decide +kernel

theorem k3617_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).1 2).1 1).1
      873891005954594063360833611593453511476509299035573525063935497911356).isSome = true := by
  decide +kernel

theorem k3617_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).1 2).1 1).2
      15752945494651579098838798241424822906403997205520081745022329878540884560202244148172).isSome = true := by
  decide +kernel

theorem k3617_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).1 2).2 1).1
      15765607337902150500597975872116264921920614455680925998258728518409507213687008912332).isSome = true := by
  decide +kernel

theorem k3617_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).1 2).2 1).2
      3940180743570835556420200687379705823762965246607809423788288845948054059030352065484).isSome = true := by
  decide +kernel

theorem k3617_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).2 2).1 1).1
      15699980000215152808491959997040446671134959984660378491754351104224401026315599068220).isSome = true := by
  decide +kernel

theorem k3617_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).2 2).1 1).2
      15695851628673405615736252003947870995720117607779591282652889097871750980593914854460).isSome = true := by
  decide +kernel

theorem k3617_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).2 2).2 1).1
      3405582934875271363132422066389973532715749677180472645847518854204).isSome = true := by
  decide +kernel

theorem k3617_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).2 2).2 1).2
      213013246179394852969893377283829959824481307297467544751331322940).isSome = true := by
  decide +kernel

theorem k3618_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).1 2).1 1).1
      15656868911916572956789701548438691950805319438593846165886929491510225109883396027964).isSome = true := by
  decide +kernel

theorem k3618_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).1 2).1 1).2
      53035336318200260724538738099074815779881028925735347250109447596).isSome = true := by
  decide +kernel

theorem k3618_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).1 2).2 1).1
      3396065977693344225893527868796356961970040875096263139135868891708).isSome = true := by
  decide +kernel

theorem k3618_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).1 2).2 1).2
      13262635912883130582705594405772376556613633478035083737662323884).isSome = true := by
  decide +kernel

theorem k3618_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).2 1).1 2).1
      52967072444493344667790662870953020452712104768965999735291115068).isSome = true := by
  decide +kernel

theorem k3618_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).2 1).1 2).2
      52984415684289180490280037943752108659924555634927909640801220156).isSome = true := by
  decide +kernel

theorem k3618_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3618) 2).1 3).2 1).2
      87170088010434421093133452651106021212066944365050088285052598121108346084596143904483651152273385156160797725815088757818648242).isSome = true := by
  decide +kernel

theorem k3618_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).2 3).1 1).1 3).1
      15677338565097059475151413508117014624653116498498308326781672420808695764128727153724).isSome = true := by
  decide +kernel

theorem k3618_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).2 3).1 1).1 3).2
      15662502247730321199655559916182781579690845483559184836690474000372110875595416386620).isSome = true := by
  decide +kernel

theorem k3618_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).2 3).1 1).2 2).1
      53071276305571075191210200403141021222154172166895666158035661372).isSome = true := by
  decide +kernel

theorem k3618_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3618) 2).2 3).1 1).2 2).2
      53088763452836040548403431384115801908646346817772112161148353596).isSome = true := by
  decide +kernel

theorem k3618_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3618) 2).2 3).2 1).1
      262756169416435064721597906387753144701075423775156564717616769472419641670157968007740508402).isSome = true := by
  decide +kernel

theorem k3618_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3618) 2).2 3).2 1).2
      4841508646932308546652147849963492774242186765658625325961112303211756352761170117856329840155396097531459389682).isSome = true := by
  decide +kernel

theorem k3619_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).1 3).1 1).1
      21768590396639083540972195992944518944247020529588860765071441684669735813373982939733297213512128341786459131950247184835136316).isSome = true := by
  decide +kernel

theorem k3619_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).1 3).1 1).2
      999547246316974461350330206354169956829632455084291566266999680623042646384224811130290).isSome = true := by
  decide +kernel

theorem k3619_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).1 3).2 1).1
      249662168557463938550742407085766623232550323444996616379240496026452295853504162286396).isSome = true := by
  decide +kernel

theorem k3619_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).1 3).2 1).2
      15602848377862538421763022372322236197189630941859993749460708756929196365333475056444).isSome = true := by
  decide +kernel

theorem k3619_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).2 3).1 1).1
      73788880150346820445380258764410161339326209063014378356920709106317421499386650788940798570172397104650812).isSome = true := by
  decide +kernel

theorem k3619_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).2 3).1 1).2
      340245837749827776746826135345522089891299582198001756054260601000520002603264837163610985896920719755602997676035797000641084).isSome = true := by
  decide +kernel

theorem k3619_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).2 3).2 1).1
      249752608779473596212201060808839915442653666381595818049981025532465713340597472844348).isSome = true := by
  decide +kernel

theorem k3619_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3619) 2).2 3).2 1).2
      846119415420743694133959541707513884347156481626059323496528861756).isSome = true := by
  decide +kernel

theorem k3620_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).1 3).1 1).1
      3381068719947469215902625592180070050966498376519513432847338654524).isSome = true := by
  decide +kernel

theorem k3620_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).1 3).1 1).2
      3898040926562264566562250714350316397595144814997091419881362606403957323738652333884).isSome = true := by
  decide +kernel

theorem k3620_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).1 3).2 1).1
      3895939077604173575680133028807647784898516052154029386268499395298053789166921009980).isSome = true := by
  decide +kernel

theorem k3620_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).1 3).2 1).2
      60873622574258132804017262969738402640783517731851306612976650736794961955099367228).isSome = true := by
  decide +kernel

theorem k3620_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).2 3).1 1).1
      52898040459543063828221111271516960981592897178161099790279374396).isSome = true := by
  decide +kernel

theorem k3620_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).2 3).1 1).2
      845460518251801730792455413955298315387030448415166943687002245948).isSome = true := by
  decide +kernel

theorem k3620_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).2 3).2 1).1
      211253998282601165064122251405608578164984433453503878508549895740).isSome = true := by
  decide +kernel

theorem k3620_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3620) 2).2 3).2 1).2
      3896942996829823652639304358661138562898510837175313519408664320541019977620246746940).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3617 3621 :=
  (Cover.one (box := dirCellBox) (n := 3617)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3617_0) (.leaf _ k3617_1)) (.split 1 (.leaf _ k3617_2) (.leaf _ k3617_3))) (.split 2 (.split 1 (.leaf _ k3617_4) (.leaf _ k3617_5)) (.split 1 (.leaf _ k3617_6) (.leaf _ k3617_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3617_8) (.leaf _ k3617_9)) (.split 1 (.leaf _ k3617_10) (.leaf _ k3617_11))) (.split 2 (.split 1 (.leaf _ k3617_12) (.leaf _ k3617_13)) (.split 1 (.leaf _ k3617_14) (.leaf _ k3617_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3618)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3618_0) (.leaf _ k3618_1)) (.split 1 (.leaf _ k3618_2) (.leaf _ k3618_3))) (.split 1 (.split 2 (.leaf _ k3618_4) (.leaf _ k3618_5)) (.leaf _ k3618_6))) (.split 3 (.split 1 (.split 3 (.leaf _ k3618_7) (.leaf _ k3618_8)) (.split 2 (.leaf _ k3618_9) (.leaf _ k3618_10))) (.split 1 (.leaf _ k3618_11) (.leaf _ k3618_12))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3619)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3619_0) (.leaf _ k3619_1)) (.split 1 (.leaf _ k3619_2) (.leaf _ k3619_3))) (.split 3 (.split 1 (.leaf _ k3619_4) (.leaf _ k3619_5)) (.split 1 (.leaf _ k3619_6) (.leaf _ k3619_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3620)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3620_0) (.leaf _ k3620_1)) (.split 1 (.leaf _ k3620_2) (.leaf _ k3620_3))) (.split 3 (.split 1 (.leaf _ k3620_4) (.leaf _ k3620_5)) (.split 1 (.leaf _ k3620_6) (.leaf _ k3620_7)))))

end C4.Cert.Dir115
