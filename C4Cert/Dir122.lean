module

public import C4Check

public section

/-! Cells `3734 ≤ n < 3763` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir122

theorem k3734_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3734) 2).1 3).1
      216247472222001783680601193686646234956193299011981423492092207512636).isSome = true := by
  decide +kernel

theorem k3734_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3734) 2).1 3).2
      3987549404145761050172450505711167042787834363915641699516834208022854439314248355855420).isSome = true := by
  decide +kernel

theorem k3734_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3734) 2).2 3).1
      13517495302374985790022286361326064434715024402833800740144835607612).isSome = true := by
  decide +kernel

theorem k3734_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3734) 2).2 3).2
      13511317378846737983182733441833318886143069364802481231761220451388).isSome = true := by
  decide +kernel

theorem k3735_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3735) 3).1 1).1
      54023939321076174247091976839407405469577995249500259859174100778044).isSome = true := by
  decide +kernel

theorem k3735_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3735) 3).1 1).2
      54023847876265401279328008370766980008398398284615418418218195696700).isSome = true := by
  decide +kernel

theorem k3735_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3735) 3).2
      104916136983909324616727784116100937911727749355091640718565793407062791219806931337431013065703127143420902238985919240276395642821644570381641265757244).isSome = true := by
  decide +kernel

theorem k3736_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3736) 3).1
      355374137141006395381097211721088861508503137941389226626344231011806178192076850285421323107946531092544729202625912003760834264124).isSome = true := by
  decide +kernel

theorem k3736_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3736) 3).2
      5551476439473429700524365934464491442327239850677202062447587417421958515432823286656689101840679163764601596996763449670547323964).isSome = true := by
  decide +kernel

theorem k3737_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3737) 3).1
      4701291954075704306776169295279817398416253151475952476997342496409094544429289890749425355297276905543908412).isSome = true := by
  decide +kernel

theorem k3737_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3737) 3).2
      3981469608034318915813511976407209552893949071050194107518167600954072044961124171070524).isSome = true := by
  decide +kernel

theorem k3738_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3738) 3).1
      3980890816181424146375435861307532365409947598769442777865129630163827262017076223228988).isSome = true := by
  decide +kernel

theorem k3738_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3738) 3).2
      4589169818081952038090690119939346185888916108876123429453239769887100449965191126234110529669911155260476).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 3739 3740 [
    88775817157875273754589005535443581641931375641535437632248354941296552627596347670639158971696201026477302032908657473033533059313] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3740 3741 [
    21663935369815890255927283711202203230651237429272392281827622287823828389574968037516197896435195170022863441769637501124959665] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3741 3756 [
    205697167755777307535382215032927384758915742116114516253474705, 147559084203055130404, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 9696021200361595054371] = true := by
  decide +kernel

theorem k3756_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3756) 3).1
      18301290744043670350013443759719617628608658610212047316441603648893409855530538125452718062510199295046).isSome = true := by
  decide +kernel

theorem k3756_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3756) 3).2
      4779997181440944299908382262927347173278194912307264768224517845546997421358823004202434136718518515780285638).isSome = true := by
  decide +kernel

theorem k3757_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3757) 3).1
      6493717623173452935093911889146734814357263859581893231511968928253835850666536145245569337089093139926510906518581792908579660641666740662145199922).isSome = true := by
  decide +kernel

theorem k3757_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3757) 3).2 2).1
      290499431138458534907582593828387336939675506140662153403539178747775754795770675804513487169180892230604).isSome = true := by
  decide +kernel

theorem k3757_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3757) 3).2 2).2
      3331348866801334616401579979361479445027635873980881102021448652).isSome = true := by
  decide +kernel

theorem k3758_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3758) 2).1 3).1
      62860917276179624264151527820405220363857751843868539982969221665467489786877943034828).isSome = true := by
  decide +kernel

theorem k3758_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3758) 2).1 3).2
      62745536943597403950807119029177022814939551307342394307448492736265433805647402316748).isSome = true := by
  decide +kernel

theorem k3758_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3758) 2).2 3).1
      3928844962189493204730350739347486932517017704107626216435490500437821424320565432012).isSome = true := by
  decide +kernel

theorem k3758_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3758) 2).2 3).2
      3922224021186466844106747159474749946833450324631824241342962492962220411506717612748).isSome = true := by
  decide +kernel

theorem k3759_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3759) 2).1 3).1
      16039852819016528119862934125776676811141208174948107173940931951590211135498228523715377).isSome = true := by
  decide +kernel

theorem k3759_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3759) 2).1 3).2
      250335959251729895180678355983811636377584432738288662119981740776572761677331626402764).isSome = true := by
  decide +kernel

theorem k3759_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3759) 2).2 3).1
      849254316155856228896451703063427340673210450432891117931203603148).isSome = true := by
  decide +kernel

theorem k3759_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3759) 2).2 3).2
      848232988940689995760843734935334630697458949560290427535433343948).isSome = true := by
  decide +kernel

theorem k3760_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3760) 2).1 3).1
      1000289786713280775209913670523827952877416916463638737314557077767217348212497792836556).isSome = true := by
  decide +kernel

theorem k3760_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3760) 2).1 3).2
      15990555669096010540623295438845270610357907512953708271811319147527270084453223269284924).isSome = true := by
  decide +kernel

theorem k3760_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3760) 2).2 3).1
      3389430428348486308302658437412383235270678941486042790250912097228).isSome = true := by
  decide +kernel

theorem k3760_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3760) 2).2 3).2
      846618535636290164863259746895404637433114596813192135748924195788).isSome = true := by
  decide +kernel

theorem k3761_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3761) 2).1 3).1
      15978541934145868637058516356845555852817442977765080253510044086448632788921261745126460).isSome = true := by
  decide +kernel

theorem k3761_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3761) 2).1 3).2
      54102829132239788444269957393890744558390632993204333666617217137724).isSome = true := by
  decide +kernel

theorem k3761_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3761) 2).2 3).1
      13535772628248508251260674891788700632991280332124094661978626997308).isSome = true := by
  decide +kernel

theorem k3761_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3761) 2).2 3).2
      13527113874849348549257527511658437820629691862801325863895028612156).isSome = true := by
  decide +kernel

theorem k3762_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3762) 2).1 3).1
      54073241912775021104512902246049401519981198977904779573254251232316).isSome = true := by
  decide +kernel

theorem k3762_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3762) 2).1 3).2
      11719732306969231143981864264345582902809268468796).isSome = true := by
  decide +kernel

theorem k3762_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3762) 2).2 1).1
      2930808179544509716258194122461457142374275365948).isSome = true := by
  decide +kernel

theorem k3762_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3762) 2).2 1).2
      13516325043470272936573799730464942054221710356125334432278973135932).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3734 3763 :=
  (Cover.one (box := dirCellBox) (n := 3734)
      (.split 2 (.split 3 (.leaf _ k3734_0) (.leaf _ k3734_1)) (.split 3 (.leaf _ k3734_2) (.leaf _ k3734_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3735)
      (.split 3 (.split 1 (.leaf _ k3735_0) (.leaf _ k3735_1)) (.leaf _ k3735_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3736)
      (.split 3 (.leaf _ k3736_0) (.leaf _ k3736_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3737)
      (.split 3 (.leaf _ k3737_0) (.leaf _ k3737_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3738)
      (.split 3 (.leaf _ k3738_0) (.leaf _ k3738_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 3756)
      (.split 3 (.leaf _ k3756_0) (.leaf _ k3756_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3757)
      (.split 3 (.leaf _ k3757_0) (.split 2 (.leaf _ k3757_1) (.leaf _ k3757_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3758)
      (.split 2 (.split 3 (.leaf _ k3758_0) (.leaf _ k3758_1)) (.split 3 (.leaf _ k3758_2) (.leaf _ k3758_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3759)
      (.split 2 (.split 3 (.leaf _ k3759_0) (.leaf _ k3759_1)) (.split 3 (.leaf _ k3759_2) (.leaf _ k3759_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3760)
      (.split 2 (.split 3 (.leaf _ k3760_0) (.leaf _ k3760_1)) (.split 3 (.leaf _ k3760_2) (.leaf _ k3760_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3761)
      (.split 2 (.split 3 (.leaf _ k3761_0) (.leaf _ k3761_1)) (.split 3 (.leaf _ k3761_2) (.leaf _ k3761_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3762)
      (.split 2 (.split 3 (.leaf _ k3762_0) (.leaf _ k3762_1)) (.split 1 (.leaf _ k3762_2) (.leaf _ k3762_3))))

end C4.Cert.Dir122
