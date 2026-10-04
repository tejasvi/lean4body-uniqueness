module

public import C4Check

public section

/-! Cells `3197 ≤ n < 3200` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir090

theorem k3197_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).1 2).1 3).1
      75945876745162901149821887082474108714747808837638484866043803964962294986956812695656205561426998958759594225).isSome = true := by
  decide +kernel

theorem k3197_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).1 2).1 3).2
      75846103885996411955553982005968164944884976081821523211513739558488736175333896681276401789140120956885780721).isSome = true := by
  decide +kernel

theorem k3197_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).1 2).2 3).1
      65905412960250445824412969926068013154911532477089651440174840848586664659947766423674669297).isSome = true := by
  decide +kernel

theorem k3197_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).1 2).2 3).2
      75894040022893268169556715592913676509382481355537913322679576347935233769304228439337788664977041539751987441).isSome = true := by
  decide +kernel

theorem k3197_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).2 2).1 1).1
      13916063495399650315990929116023393506010271830256012534105559535618291).isSome = true := by
  decide +kernel

theorem k3197_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).2 2).1 1).2
      15654223757396866253047725857837506603962681423282205348658084252218814241546625771955).isSome = true := by
  decide +kernel

theorem k3197_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).2 2).2 1).1
      18502688049502976926819404796457601515758368186091582276947631713084895352129204153806837283409803788409404).isSome = true := by
  decide +kernel

theorem k3197_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).1 3).2 2).2 1).2
      18498731184784691752507039564487757081351073122910927124242551584973526355584663467263226138504111239033660).isSome = true := by
  decide +kernel

theorem k3197_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).1 2).1 3).1
      263814344075824603757416664220293886729485095583032371537023233595371281108874435128469473521).isSome = true := by
  decide +kernel

theorem k3197_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).1 2).1 3).2
      65855839723003171208958187260140049900677604109058385781681714427144068167585410526232430833).isSome = true := by
  decide +kernel

theorem k3197_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).1 2).2 3).1
      16500029972517368942648188787351719790982573356134946688646364675480343705604621580644053233).isSome = true := by
  decide +kernel

theorem k3197_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).1 2).2 3).2
      16474524748513354169202812168357327182539697425181205840570394168638451609190523094108139761).isSome = true := by
  decide +kernel

theorem k3197_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).2 2).1 1).1
      65723188675482294455278138490482052315556844999588929395017760936058169282518659401046804723).isSome = true := by
  decide +kernel

theorem k3197_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).2 2).1 1).2
      250809952662854551488224784686314348243582134781092171853359084681105040393917685553724).isSome = true := by
  decide +kernel

theorem k3197_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).2 2).2 1).1
      16438757209133944320723917529417776719728847297691316042348922352237084264368228441914732787).isSome = true := by
  decide +kernel

theorem k3197_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3197) 2).2 3).2 2).2 1).2
      1005604800157284528329378191639036616460977225492252273746821241448892274435038470195772).isSome = true := by
  decide +kernel

theorem k3198_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).1 2).1 1).1
      52987979655779872929388891487375521519994873858298061796816813484).isSome = true := by
  decide +kernel

theorem k3198_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).1 2).1 1).2
      3909479471609833593179274998835151021755917500017886972374801577901950903269092480828).isSome = true := by
  decide +kernel

theorem k3198_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).1 2).2 1).1
      47050420172448973808530473740308896457255270118067).isSome = true := by
  decide +kernel

theorem k3198_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).1 2).2 1).2
      848727277351473103390214192769554592214628804270100153871076641596).isSome = true := by
  decide +kernel

theorem k3198_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).2 1).1 3).1
      52940016468550921326102383162655494423814928799645615795871281836).isSome = true := by
  decide +kernel

theorem k3198_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).2 1).1 3).2
      61014270894050549770798225505747844506368969148501899102407377294358923677897482092).isSome = true := by
  decide +kernel

theorem k3198_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3198) 2).1 3).2 1).2
      348376055357830824921497734310003430849776958114730458547593919563922251669409067504887473905965169496980850156813517159656706994).isSome = true := by
  decide +kernel

theorem k3198_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).1 2).1 1).1
      1001552092780880885118614667810778073702316785654623983393881795338992451714305002293820).isSome = true := by
  decide +kernel

theorem k3198_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).1 2).1 1).2
      62664193405942767307691538109747137352779758905862894432465366602242874421530119332668).isSome = true := by
  decide +kernel

theorem k3198_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).1 2).2 1).1
      250491339265934926884118648970984064155294641842134664888380150359714003996941135376956).isSome = true := by
  decide +kernel

theorem k3198_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).1 2).2 1).2
      250446773438236429485429996078042230319854970124831740299860677783432833372415328246332).isSome = true := by
  decide +kernel

theorem k3198_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).2 1).1 3).1
      53025274982261943867626696049195257550035950041336044424861708860).isSome = true := by
  decide +kernel

theorem k3198_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).2 1).1 3).2
      52940706532961660992266230387574272425154416053251724763166274108).isSome = true := by
  decide +kernel

theorem k3198_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).2 1).2 2).1
      52943711205012705866048112096496691827650283973919983911720842812).isSome = true := by
  decide +kernel

theorem k3198_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3198) 2).2 3).2 1).2 2).2
      52959457167623181947000394018475186147258121641070133812857796156).isSome = true := by
  decide +kernel

theorem k3199_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).1 3).1 1).1
      21246590492890395081780527269214426557752752711158849510941823775757087575410353140102905593652502755161307057799422301396402).isSome = true := by
  decide +kernel

theorem k3199_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).1 3).1 1).2
      339896302394394608134775076694665587447170136406264835257147766017341998685322379308860491963721778631159405718820317514790130).isSome = true := by
  decide +kernel

theorem k3199_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).1 3).2 1).1
      287692217383925632514390916664764147047744169108255438491629698804541748115003701225182287236117078463292).isSome = true := by
  decide +kernel

theorem k3199_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).1 3).2 1).2
      71923094429127980319366212920410183371616893522425073060118545226933544576510078460639339979400167814578).isSome = true := by
  decide +kernel

theorem k3199_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).2 3).1 1).1
      1360223832251812242161163332437270465469776851336739100351641342871529637229431033016135055940608161773584780913767398999317052).isSome = true := by
  decide +kernel

theorem k3199_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).2 3).1 1).2
      18875735803795354311310113712551825484196135390321532628339381161116315104173542258850558624009247978537776818).isSome = true := by
  decide +kernel

theorem k3199_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).2 3).2 1).1
      62383724470590508568756870070357163238402126280166472843491971749516227726794424016051).isSome = true := by
  decide +kernel

theorem k3199_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3199) 2).2 3).2 1).2
      3903670352567360065059294476015387404614819139885618861895678147875345397611687826236).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3197 3200 :=
  (Cover.one (box := dirCellBox) (n := 3197)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3197_0) (.leaf _ k3197_1)) (.split 3 (.leaf _ k3197_2) (.leaf _ k3197_3))) (.split 2 (.split 1 (.leaf _ k3197_4) (.leaf _ k3197_5)) (.split 1 (.leaf _ k3197_6) (.leaf _ k3197_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3197_8) (.leaf _ k3197_9)) (.split 3 (.leaf _ k3197_10) (.leaf _ k3197_11))) (.split 2 (.split 1 (.leaf _ k3197_12) (.leaf _ k3197_13)) (.split 1 (.leaf _ k3197_14) (.leaf _ k3197_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3198)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3198_0) (.leaf _ k3198_1)) (.split 1 (.leaf _ k3198_2) (.leaf _ k3198_3))) (.split 1 (.split 3 (.leaf _ k3198_4) (.leaf _ k3198_5)) (.leaf _ k3198_6))) (.split 3 (.split 2 (.split 1 (.leaf _ k3198_7) (.leaf _ k3198_8)) (.split 1 (.leaf _ k3198_9) (.leaf _ k3198_10))) (.split 1 (.split 3 (.leaf _ k3198_11) (.leaf _ k3198_12)) (.split 2 (.leaf _ k3198_13) (.leaf _ k3198_14)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3199)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3199_0) (.leaf _ k3199_1)) (.split 1 (.leaf _ k3199_2) (.leaf _ k3199_3))) (.split 3 (.split 1 (.leaf _ k3199_4) (.leaf _ k3199_5)) (.split 1 (.leaf _ k3199_6) (.leaf _ k3199_7)))))

end C4.Cert.Dir090
