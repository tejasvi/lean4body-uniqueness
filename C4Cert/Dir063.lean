module

public import C4Check

public section

/-! Cells `2777 ≤ n < 2802` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir063

theorem k2777_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 2).1 3).1
      74007436735684015773975594102735937556576536319165667782332788707619940389449898139764285681332047691742385).isSome = true := by
  decide +kernel

theorem k2777_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 2).1 3).2
      1155623838302291665241664535000592605091399940693406534557799297089434018218127644698821251914689581571249).isSome = true := by
  decide +kernel

theorem k2777_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 2).2 3).1
      21858457271753377373835482969980981469989406310036029689499644646959513773723631720926210660356277586241806283434984764137168689).isSome = true := by
  decide +kernel

theorem k2777_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 2).2 3).2
      73971873235141537830631446544543095623239316511662853026767268826079356721176212408188935618120110991310001).isSome = true := by
  decide +kernel

theorem k2777_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).2 2).1 1).1
      62549136190832029897003416483097846143732804960269940256828526512947986561127595859123).isSome = true := by
  decide +kernel

theorem k2777_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).2 2).1 1).2
      72115000515296972625545734709991874221862411125914813803758289589747178169565867827131178427049620233651).isSome = true := by
  decide +kernel

theorem k2777_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).2 2).2 1).1
      62569358208225690411877674614988753600836608581264932310107206899388008709623477853363).isSome = true := by
  decide +kernel

theorem k2777_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).2 2).2 1).2
      18473395319737042213404705863275574497904264366190987109130218294051881192898248762457227042119997521349868).isSome = true := by
  decide +kernel

theorem k2777_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).1 2).1 3).1
      4742953367256028287645298048910327867220017953240333224666439663472557188753109116132714738700890534626012977).isSome = true := by
  decide +kernel

theorem k2777_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).1 2).1 3).2
      21847226683752067637991332560006457499403950751134249002391099283376721565272170842250241434874786089103639684127092515792117553).isSome = true := by
  decide +kernel

theorem k2777_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).1 2).2 3).1
      4746321842739541200941590606247697792386693089984169771987280788892473461438939443903988818916191728610725681).isSome = true := by
  decide +kernel

theorem k2777_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).1 2).2 3).2
      18960913768749051714200445935999921208367892707953334821993469701605050126977023006278154227497399775120666417).isSome = true := by
  decide +kernel

theorem k2777_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).2 2).1 1).1
      15648506204527092832828226243028487817309413031206053866708513999015909234467599440691).isSome = true := by
  decide +kernel

theorem k2777_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).2 2).1 1).2
      62577466607254527872989100051967846380471902971551064439402521880102524105159906516147).isSome = true := by
  decide +kernel

theorem k2777_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).2 2).2 1).1
      250471272380383762602328580663184034694226216905468769562422119005284784820364743908147).isSome = true := by
  decide +kernel

theorem k2777_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).2 2).2 1).2
      73908632742434829486291986763676419088305403797401874939162804185163206487350440111165714557746936855231667).isSome = true := by
  decide +kernel

theorem k2778_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).1 2).1
      1361027238520273991358963826346397718320040225831171959052943824446046345444294296987290259453995716331546859389164455421399985).isSome = true := by
  decide +kernel

theorem k2778_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).1 2).2 1).1
      211906671900096230940852343452744116568680166848827055307065941171).isSome = true := by
  decide +kernel

theorem k2778_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).1 2).2 1).2
      976708608226013054612379702859203816339271618295720912370094359349249425627075179756).isSome = true := by
  decide +kernel

theorem k2778_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).2 2).1
      72094525677846986621316910564680296420145470392800210871086012953878484604168772974343850164781225440497).isSome = true := by
  decide +kernel

theorem k2778_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).2 2).2
      84999417944228518533053148728103637401402516673168419400088933793411921049065574865604148675727270098846132993448857590717873).isSome = true := by
  decide +kernel

theorem k2778_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).1 1).1 2).1
      977038117684774453626135885916938480341462297723899951980572283867248365889111555244).isSome = true := by
  decide +kernel

theorem k2778_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).1 1).1 2).2
      3907931859673052456308963778210758308067590681955478875926218401818355718293411600179).isSome = true := by
  decide +kernel

theorem k2778_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).1 1).2 3).1
      212144723235494408639284719580722025360866169711652395453723278508).isSome = true := by
  decide +kernel

theorem k2778_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).1 1).2 3).2
      976762211370885212480142751108242717977283922991147283530656080191348355163393719468).isSome = true := by
  decide +kernel

theorem k2778_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).2 2).1
      21254606239975093796766118168240687317133967505946499302323855782964738967282694154572597329404711077621940662511597390355889).isSome = true := by
  decide +kernel

theorem k2778_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).2 2).2 1).1
      13229737659411895499933474076134264580523180764351073197819002028).isSome = true := by
  decide +kernel

theorem k2778_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).2 2).2 1).2
      244037338310751927781690529228580359731997173931073863939087433094406535723529895340).isSome = true := by
  decide +kernel

theorem k2779_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2779) 2).1 3).1
      7399081108626579151792846661898602882098942147899161167757917652039072103116384093925533720651452565562527705038898585853450736999602918178111607119064090126233318857).isSome = true := by
  decide +kernel

theorem k2779_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2779) 2).1 3).2
      71966275242459163960416193899864392632569310092378738883309038409927561808702140254736349711742625569353).isSome = true := by
  decide +kernel

theorem k2779_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2779) 2).2 3).1 1).1
      62399831844789199553217712294669427685417152925564417864362729837715609648286695054515).isSome = true := by
  decide +kernel

theorem k2779_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2779) 2).2 3).1 1).2
      21240179806150262056537557134502669336325870798790901903732951614844260973525172365794341432099768021401783240260131019185586).isSome = true := by
  decide +kernel

theorem k2779_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2779) 2).2 3).2 1).1
      17979454660286187716439031529482919404823866043431778481766850904321479069438967346428887494357892866418).isSome = true := by
  decide +kernel

theorem k2779_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2779) 2).2 3).2 1).2
      60912831906994785375352695385852584562308455503679063708199687752705724756819275122).isSome = true := by
  decide +kernel

theorem k2780_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2780) 2).1
      16333837221217344426785001628655388634951508112458188251881247434622103465050482395232403806).isSome = true := by
  decide +kernel

theorem k2780_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2780) 2).2 3).1
      339418991534220385433152688343688659717276529085967711617577628155561812011840768817441609326227087316559347413257275275858865).isSome = true := by
  decide +kernel

theorem k2780_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2780) 2).2 3).2
      17973230218850087528417663074472061283152801509906609940509234072514819187876713633130031067264778868553).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 2781 2801 [
    308343740213660245183060715369435551457075353627030048606539712065179139396163454810761202376364890320894073987094,
    65906, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2801 2802 [
    3035621286543125269436410217908291029321124409424600864690495590275556470643495472478937812122250495372739927596100334701528120576661587891] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2777 2802 :=
  (Cover.one (box := dirCellBox) (n := 2777)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2777_0) (.leaf _ k2777_1)) (.split 3 (.leaf _ k2777_2) (.leaf _ k2777_3))) (.split 2 (.split 1 (.leaf _ k2777_4) (.leaf _ k2777_5)) (.split 1 (.leaf _ k2777_6) (.leaf _ k2777_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k2777_8) (.leaf _ k2777_9)) (.split 3 (.leaf _ k2777_10) (.leaf _ k2777_11))) (.split 2 (.split 1 (.leaf _ k2777_12) (.leaf _ k2777_13)) (.split 1 (.leaf _ k2777_14) (.leaf _ k2777_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2778)
      (.split 2 (.split 3 (.split 2 (.leaf _ k2778_0) (.split 1 (.leaf _ k2778_1) (.leaf _ k2778_2))) (.split 2 (.leaf _ k2778_3) (.leaf _ k2778_4))) (.split 3 (.split 1 (.split 2 (.leaf _ k2778_5) (.leaf _ k2778_6)) (.split 3 (.leaf _ k2778_7) (.leaf _ k2778_8))) (.split 2 (.leaf _ k2778_9) (.split 1 (.leaf _ k2778_10) (.leaf _ k2778_11)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2779)
      (.split 2 (.split 3 (.leaf _ k2779_0) (.leaf _ k2779_1)) (.split 3 (.split 1 (.leaf _ k2779_2) (.leaf _ k2779_3)) (.split 1 (.leaf _ k2779_4) (.leaf _ k2779_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2780)
      (.split 2 (.leaf _ k2780_0) (.split 3 (.leaf _ k2780_1) (.leaf _ k2780_2)))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5)

end C4.Cert.Dir063
