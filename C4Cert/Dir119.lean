module

public import C4Check

public section

/-! Cells `3674 ≤ n < 3683` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir119

theorem k3674_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).1 3).1 1).1
      87599459759283885148017131476132926303373838071522909974749250332808026346814204736529528278979859133526395587559012395967263692).isSome = true := by
  decide +kernel

theorem k3674_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).1 3).1 1).2
      16072501749169470119918957202170885081948645388511108501831598236207511050778041374841650).isSome = true := by
  decide +kernel

theorem k3674_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).1 3).2 1).1
      1002846424168252822298311706765626007222297743611412521531031376276104649738121079528242).isSome = true := by
  decide +kernel

theorem k3674_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).1 3).2 1).2
      250650237508410253754263938068079418231173842691277982833296789358135985360067907407564).isSome = true := by
  decide +kernel

theorem k3674_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).2 3).1 1).1
      251245016543653626779381176961994202274794752873841441098341851519490294543590166063820).isSome = true := by
  decide +kernel

theorem k3674_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).2 3).1 1).2
      13952262757383845124915842521929546246424083724835671681096667988699954).isSome = true := by
  decide +kernel

theorem k3674_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).2 3).2 1).1
      250778014773755830967657047229351904069301044103600052618090117739314483854392030096076).isSome = true := by
  decide +kernel

theorem k3674_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3674) 2).2 3).2 1).2
      212388842371302564433699705276167674457838827700729872294654499532).isSome = true := by
  decide +kernel

theorem k3675_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).1 3).1 1).1
      54278336821395872925550742949817869461703473275799719358386782551100).isSome = true := by
  decide +kernel

theorem k3675_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).1 3).1 1).2
      250287155896430127188574708348393035904366086661628714580079169462129053699350634216508).isSome = true := by
  decide +kernel

theorem k3675_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).1 3).2 1).1
      3388295114062390087320065618947401354980451798998003567007127878716).isSome = true := by
  decide +kernel

theorem k3675_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).1 3).2 1).2
      13551859622225771956676061881400122500239389434619623439817591929916).isSome = true := by
  decide +kernel

theorem k3675_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).2 3).1 1).1
      848379799364548452704209683268048643886186742740073062115879898828).isSome = true := by
  decide +kernel

theorem k3675_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).2 3).1 1).2
      53017471466077709108682216534165437266509486478170377316502235852).isSome = true := by
  decide +kernel

theorem k3675_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).2 3).2 1).1
      62527072732482987951224795074975417120138626770609084688183682149580532542048887585852).isSome = true := by
  decide +kernel

theorem k3675_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3675) 2).2 3).2 1).2
      3388981003553669787602759239554091108522614028621176131830565497916).isSome = true := by
  decide +kernel

theorem k3676_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3676) 2).1 3).1 1).1
      15611475293810938586441352460550596074707325263670245263937016896829537748547488562236).isSome = true := by
  decide +kernel

theorem k3676_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3676) 2).1 3).1 1).2
      15610197549817843272716645582722303358478709941259844123384479855701115343207296515132).isSome = true := by
  decide +kernel

theorem k3676_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3676) 2).1 3).2 1).1
      3382467531274392527436437965194041058035004541300019683280748919868).isSome = true := by
  decide +kernel

theorem k3676_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3676) 2).1 3).2 1).2
      13225331949349622560652273482845015736949065713798433627283487804).isSome = true := by
  decide +kernel

theorem k3676_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3676) 2).2 3).1 1).1
      3386075485380344906303491410456210198347101781779780626786138504252).isSome = true := by
  decide +kernel

theorem k3676_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3676) 2).2 3).1 1).2
      45883565560912325596422507815709102806892522556).isSome = true := by
  decide +kernel

theorem k3676_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3676) 2).2 3).2
      19322274759578389954838679176404602786083190177399408462411090574345295296992827937994689303924092260099273453809).isSome = true := by
  decide +kernel

theorem k3677_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3677) 2).1 3).1
      261530701582582438813620052587142421386719900434078441009202568237448876934443286180159539441).isSome = true := by
  decide +kernel

theorem k3677_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3677) 2).1 3).2
      4709117501902180221942221504200677782195252039227491765456446312974582226624042157355696612804092837823816508).isSome = true := by
  decide +kernel

theorem k3677_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3677) 2).2 3).1
      1206391842810432666161964914440514215502248094784611313084774475734469926429646349821053750422379209543909098300).isSome = true := by
  decide +kernel

theorem k3677_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3677) 2).2 3).2
      63830440207195953475957800549100733475242264508225061623933484000948367546699489865614140).isSome = true := by
  decide +kernel

theorem k3678_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3678) 2).1 3).1
      1176781775388807498714167951001366728159215404327777180831260182656289910161700899972345007368305839836177212).isSome = true := by
  decide +kernel

theorem k3678_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3678) 2).1 3).2
      249106124871449078018134101083417939618222713372044147980606937361271531884104961215036).isSome = true := by
  decide +kernel

theorem k3678_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3678) 2).2 3).1
      1176981383890261256811223004664971900037337504467119786591559261161408506907242473937539928900916151375045436).isSome = true := by
  decide +kernel

theorem k3678_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3678) 2).2 3).2
      294134616814725815471742597213736192766966365075134875148821439908530110382442727109210134488896514838963004).isSome = true := by
  decide +kernel

theorem k3679_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3679) 2).1 3).1
      843741345629358352967919297901829739112105530469665277440656132668).isSome = true := by
  decide +kernel

theorem k3679_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3679) 2).1 3).2
      3374147049318376294686896515128547747314692716395136955839831067196).isSome = true := by
  decide +kernel

theorem k3679_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3679) 2).2 3).1
      249063134395163016935434019647768382680484381322357496698175983440227918700272370565948).isSome = true := by
  decide +kernel

theorem k3679_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3679) 2).2 3).2
      210904499360479838951078274855765061062497711612799687550284722748).isSome = true := by
  decide +kernel

theorem k3680_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3680) 3).1 1).1
      972859987663716571736889239776614879529120771260669983930937244147740450098121636924).isSome = true := by
  decide +kernel

theorem k3680_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3680) 3).1 1).2
      210851714427326875500296989313187691412952929137398380303682499132).isSome = true := by
  decide +kernel

theorem k3680_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3680) 3).2 2).1
      52700990760799955414995492303413606503421967869841905032176847420).isSome = true := by
  decide +kernel

theorem k3680_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3680) 3).2 2).2
      3888903309639568579824084912536133282541231283471098071122788477860278186647833932348).isSome = true := by
  decide +kernel

theorem k3681_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3681) 3).1
      5549530073788836420180289725613252130812403048490555744337666664883545278435384960224795601745923914129563611399784264955638262002).isSome = true := by
  decide +kernel

theorem k3681_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3681) 3).2
      73435895374303882015337292701634739056811153783652969458789872577864494009722978293242748961086068875425010).isSome = true := by
  decide +kernel

theorem k3682_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3682) 2).1
      5293360839412608620019133019860691507514060136999374612252638939726762875943599494208396872425203957316762307972865820448572).isSome = true := by
  decide +kernel

theorem k3682_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3682) 2).2
      3980096161934386683203836108675255008697823964626868349856585452987175676044064703498483).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3674 3683 :=
  (Cover.one (box := dirCellBox) (n := 3674)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3674_0) (.leaf _ k3674_1)) (.split 1 (.leaf _ k3674_2) (.leaf _ k3674_3))) (.split 3 (.split 1 (.leaf _ k3674_4) (.leaf _ k3674_5)) (.split 1 (.leaf _ k3674_6) (.leaf _ k3674_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3675)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3675_0) (.leaf _ k3675_1)) (.split 1 (.leaf _ k3675_2) (.leaf _ k3675_3))) (.split 3 (.split 1 (.leaf _ k3675_4) (.leaf _ k3675_5)) (.split 1 (.leaf _ k3675_6) (.leaf _ k3675_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3676)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3676_0) (.leaf _ k3676_1)) (.split 1 (.leaf _ k3676_2) (.leaf _ k3676_3))) (.split 3 (.split 1 (.leaf _ k3676_4) (.leaf _ k3676_5)) (.leaf _ k3676_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3677)
      (.split 2 (.split 3 (.leaf _ k3677_0) (.leaf _ k3677_1)) (.split 3 (.leaf _ k3677_2) (.leaf _ k3677_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3678)
      (.split 2 (.split 3 (.leaf _ k3678_0) (.leaf _ k3678_1)) (.split 3 (.leaf _ k3678_2) (.leaf _ k3678_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3679)
      (.split 2 (.split 3 (.leaf _ k3679_0) (.leaf _ k3679_1)) (.split 3 (.leaf _ k3679_2) (.leaf _ k3679_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3680)
      (.split 3 (.split 1 (.leaf _ k3680_0) (.leaf _ k3680_1)) (.split 2 (.leaf _ k3680_2) (.leaf _ k3680_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3681)
      (.split 3 (.leaf _ k3681_0) (.leaf _ k3681_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3682)
      (.split 2 (.leaf _ k3682_0) (.leaf _ k3682_1)))

end C4.Cert.Dir119
