module

public import C4Check

public section

/-! Cells `3683 ≤ n < 3707` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir120

theorem k3683_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3683) 2).1
      15181146535239767763829105898296831068278757997276606610147620013759640445530338673).isSome = true := by
  decide +kernel

theorem k3683_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3683) 2).2
      3886450047974728771674156319493532773449200763221198875670894474400176070485441141937).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 3684 3685 [
    286776586625890713953100672452695843863194073266790336286787722817923713997642482853152821760734765617990] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3685 3699 [
    242839406503566246809158799186908207520070528460484422027041006985836562683680217673,
    2361026563773332042817, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3699_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3699) 3).1
      1004248288905223737226883991368284031288348469557205025158061597372174795516525980235).isSome = true := by
  decide +kernel

theorem k3699_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3699) 3).2 2).1
      18876980398591125217932505753873756024353961000294263837035561552130034883896414137118196203797329021464141).isSome = true := by
  decide +kernel

theorem k3699_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3699) 3).2 2).2
      62382866531703004787262743732602584013653543128552108702392212410505878315821157745).isSome = true := by
  decide +kernel

theorem k3700_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3700) 3).1 2).1
      22667131830599878068274508235912399453549795404859403788125251688698418896870999404530799427612678245161435894383135634407700484813).isSome = true := by
  decide +kernel

theorem k3700_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3700) 3).1 2).2
      15888052688635780723563709924597959437184801701825149947781899381379860912306261613745).isSome = true := by
  decide +kernel

theorem k3700_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3700) 3).2 2).1
      1412737428586919517126989084591994487182870485864726523416821342038882030055068457735361747667269411217817292009513555553408593713).isSome = true := by
  decide +kernel

theorem k3700_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3700) 3).2 2).2
      88311734735225282182507966031947622684238301608016631302951029007173744707867625888279465436909017473108027985924306076511457074).isSome = true := by
  decide +kernel

theorem k3701_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3701) 2).1 3).1 1).1
      53488612994474609380164732230840039925032249964164746365273788108).isSome = true := by
  decide +kernel

theorem k3701_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3701) 2).1 3).1 1).2
      3944045344356746000700685621915910082787613973437926639933983877696952103386010344140).isSome = true := by
  decide +kernel

theorem k3701_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3701) 2).1 3).2 1).1
      853439916232196029633906810370038886246348116357267120729591074508).isSome = true := by
  decide +kernel

theorem k3701_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3701) 2).1 3).2 1).2
      3935126295850672344951940690538799149476032755441117292846770489934716033862829857484).isSome = true := by
  decide +kernel

theorem k3701_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3701) 2).2 3).1
      21992117642467201821692361094571297631397331695993821422430829956676730260177068834539557112682604068304996670024603121055387441).isSome = true := by
  decide +kernel

theorem k3701_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3701) 2).2 3).2 1).1
      723036741340440240737059283134660393424247500).isSome = true := by
  decide +kernel

theorem k3701_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3701) 2).2 3).2 1).2
      3935917684122080317744309274487011692528915965443622403190234193709394747698634545868).isSome = true := by
  decide +kernel

theorem k3702_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).1 3).1 1).1
      212879696524775292127816163284031863538665127286095500240458603212).isSome = true := by
  decide +kernel

theorem k3702_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).1 3).1 1).2
      212837118355233860991495856370876913544360608391684657468182874828).isSome = true := by
  decide +kernel

theorem k3702_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).1 3).2 1).1
      212488573748398368499478044471882202886055117048231021855890725580).isSome = true := by
  decide +kernel

theorem k3702_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).1 3).2 1).2
      212448820274639923182936409381970405369257161897456890701776669388).isSome = true := by
  decide +kernel

theorem k3702_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).2 3).1 1).1
      13307955054946871461123908686182724947809276065888886835461462732).isSome = true := by
  decide +kernel

theorem k3702_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).2 3).1 1).2
      212889105017597843307691438409697519660164413398329499137290521292).isSome = true := by
  decide +kernel

theorem k3702_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).2 3).2 1).1
      212538740639741967289935658114036381358200654605612650442295597772).isSome = true := by
  decide +kernel

theorem k3702_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3702) 2).2 3).2 1).2
      53126394481660697317201797864272498455524263537586543768409338572).isSome = true := by
  decide +kernel

theorem k3703_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3703) 2).1 3).1 1).1
      848672812904633340652957002192277694046593479824893586030867735500).isSome = true := by
  decide +kernel

theorem k3703_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3703) 2).1 3).1 1).2
      212140604771427377108914304338784268409924579431018912552865749708).isSome = true := by
  decide +kernel

theorem k3703_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3703) 2).1 3).2 1).1
      211896525457125819589991328552635116396811550726190848364571515596).isSome = true := by
  decide +kernel

theorem k3703_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3703) 2).1 3).2 1).2
      13242276587046000628199990500140389202227860825128133033777928908).isSome = true := by
  decide +kernel

theorem k3703_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3703) 2).2 3).1
      4845521384818931297783999294358250489470077524082966540911934365195864061375254972925676596610518274944008137521).isSome = true := by
  decide +kernel

theorem k3703_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3703) 2).2 3).2
      4197512824177687617437297304541857812997271556662530921878173961041911410899523748658711138097).isSome = true := by
  decide +kernel

theorem k3704_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3704) 2).1 3).1 1).1
      13229741227139007201913755594427923107123105772165504100046707404).isSome = true := by
  decide +kernel

theorem k3704_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3704) 2).1 3).1 1).2
      13228820080849586800493526799134677526207000486267895011683572428).isSome = true := by
  decide +kernel

theorem k3704_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3704) 2).1 3).2
      65451633311647181721794212452081594464325465219601183984651070006990809233286384201269227761).isSome = true := by
  decide +kernel

theorem k3704_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3704) 2).2 3).1
      1208715900504222345481962915914191518618287749717857990808401555576927635348985594122907505544450001030635273276).isSome = true := by
  decide +kernel

theorem k3704_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3704) 2).2 3).2
      5569549415283551466877232913778517723512012678554237906833842515376444214241593292973978810683150013978821520947522009786756054076).isSome = true := by
  decide +kernel

theorem k3705_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3705) 2).1 3).1
      347790385916086457437621954485646891151044126419725003713973919789688061070166721500538161938645894258626759509846632412280044604).isSome = true := by
  decide +kernel

theorem k3705_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3705) 2).1 3).2
      865185670586079385451827130293903428426706995387087773945745091247164).isSome = true := by
  decide +kernel

theorem k3705_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3705) 2).2 3).1
      255551892867126746610159432353434372367592561046489810369331882576034310758130684565077052).isSome = true := by
  decide +kernel

theorem k3705_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3705) 2).2 3).2
      15962747530042454744021689587820881464507615054892507307903073720188054600248050594921532).isSome = true := by
  decide +kernel

theorem k3706_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3706) 2).1 3).1
      3988245625849894239079060978443761720508405569260356579853160811411026145998320778855228).isSome = true := by
  decide +kernel

theorem k3706_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3706) 2).1 3).2
      3986620345853190563018135027361784968513528698846790489802063429395006747807419834549052).isSome = true := by
  decide +kernel

theorem k3706_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3706) 2).2 3).1
      997173939236186254752969490919124345787206857459167367982578172085703986145748240350268).isSome = true := by
  decide +kernel

theorem k3706_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3706) 2).2 3).2
      54033295617401242725843789541951706572690830333578928387957047082044).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3683 3707 :=
  (Cover.one (box := dirCellBox) (n := 3683)
      (.split 2 (.leaf _ k3683_0) (.leaf _ k3683_1))).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 3699)
      (.split 3 (.leaf _ k3699_0) (.split 2 (.leaf _ k3699_1) (.leaf _ k3699_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3700)
      (.split 3 (.split 2 (.leaf _ k3700_0) (.leaf _ k3700_1)) (.split 2 (.leaf _ k3700_2) (.leaf _ k3700_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3701)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3701_0) (.leaf _ k3701_1)) (.split 1 (.leaf _ k3701_2) (.leaf _ k3701_3))) (.split 3 (.leaf _ k3701_4) (.split 1 (.leaf _ k3701_5) (.leaf _ k3701_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3702)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3702_0) (.leaf _ k3702_1)) (.split 1 (.leaf _ k3702_2) (.leaf _ k3702_3))) (.split 3 (.split 1 (.leaf _ k3702_4) (.leaf _ k3702_5)) (.split 1 (.leaf _ k3702_6) (.leaf _ k3702_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3703)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3703_0) (.leaf _ k3703_1)) (.split 1 (.leaf _ k3703_2) (.leaf _ k3703_3))) (.split 3 (.leaf _ k3703_4) (.leaf _ k3703_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3704)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3704_0) (.leaf _ k3704_1)) (.leaf _ k3704_2)) (.split 3 (.leaf _ k3704_3) (.leaf _ k3704_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3705)
      (.split 2 (.split 3 (.leaf _ k3705_0) (.leaf _ k3705_1)) (.split 3 (.leaf _ k3705_2) (.leaf _ k3705_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3706)
      (.split 2 (.split 3 (.leaf _ k3706_0) (.leaf _ k3706_1)) (.split 3 (.leaf _ k3706_2) (.leaf _ k3706_3))))

end C4.Cert.Dir120
