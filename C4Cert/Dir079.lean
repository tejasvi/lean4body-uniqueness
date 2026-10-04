module

public import C4Check

public section

/-! Cells `3137 ≤ n < 3138` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir079

theorem k3137_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).1 3).1
      25003342572799958944192827833111617072060522262562743697156499867012260362930160110002359320590965043308011237943537649661382).isSome = true := by
  decide +kernel

theorem k3137_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).1 3).2 2).1
      24496900273228616979706642234925046065362088525513267969468058355376119018948817236530343244613421773297380844312460794309709).isSome = true := by
  decide +kernel

theorem k3137_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).1 3).2 2).2
      17615622693866270372658920445392987129014355779281253840209557631567488997266969969).isSome = true := by
  decide +kernel

theorem k3137_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).2 3).1
      72725076991312092761498666338082683707644692426062355568667068823146439839521827398).isSome = true := by
  decide +kernel

theorem k3137_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).2 3).2
      20735169282250427244166245640783126742929506631738502230668623515707333947116987302725049124319031793734).isSome = true := by
  decide +kernel

theorem k3137_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).1 3).1 2).1
      23961938358335254436069506884680997377607183926586016758667320287457355060241579936066578464742883121561802440686206503837105).isSome = true := by
  decide +kernel

theorem k3137_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).1 3).1 2).2
      81473974563484957450431391990982679363116042545525157266780415715021854355021894692023453149843312727473).isSome = true := by
  decide +kernel

theorem k3137_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).1 3).2 2).1
      4412192978978620128180742176553869004469214897670840361017876961873163057384798687370673).isSome = true := by
  decide +kernel

theorem k3137_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).1 3).2 2).2
      319993714979130495656188945171291435280769957076440667459544912854974222040724544609535559195286784465329).isSome = true := by
  decide +kernel

theorem k3137_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).2 3).1
      526292382487754123313937069417793478457936692890732384696191689287212291672407661063929370543803899875299783679693038168118811738021514924626508852433622163697948102).isSome = true := by
  decide +kernel

theorem k3137_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).2 3).2
      1784639743365098375594839521671059239954877622586682672897517838258142475972530489288461556212675395232681141446070058080298864932176639879290328774).isSome = true := by
  decide +kernel

theorem k3137_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).1 3).1 2).1
      23714513917966397091411870620583081980569381963117646941819135551177213239129049137792302606312700600601220788850779884926396081).isSome = true := by
  decide +kernel

theorem k3137_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).1 3).1 2).2
      17048483106790000851068067927562757136913718678536558199584464345452872792686342363569).isSome = true := by
  decide +kernel

theorem k3137_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).1 3).2 2).1
      4408758410742585623090357126125964326577740354358532934038121119007106679219785458398917298).isSome = true := by
  decide +kernel

theorem k3137_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).1 3).2 2).2
      19882246897869958293482592631791624673885077890912613343064366790081100991042104174855380720785365439183281).isSome = true := by
  decide +kernel

theorem k3137_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).2 3).1 2).1
      17086416530111404016360690873844547429323445820373643400404588742335018636544298666812).isSome = true := by
  decide +kernel

theorem k3137_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).2 3).1 2).2
      1069968330816413459536944895838434691570736514303831203605922214607750468766840255724).isSome = true := by
  decide +kernel

theorem k3137_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).2 3).2 2).1
      16912287959310417413310024500478636807062698464205917564409896578813706743175435966897).isSome = true := by
  decide +kernel

theorem k3137_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).2 3).2 2).2
      1059843582705837828435034362083280187756595544925875930076131986835947147307860227308).isSome = true := by
  decide +kernel

theorem k3137_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).1 2).1 3).1
      313788321288312032627666944037335398732139205271398508786524344752922254734830949951245412227254064755630769).isSome = true := by
  decide +kernel

theorem k3137_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).1 2).1 3).2
      16853316212001673265735870137518649921365849089226135741219608086780557677898318612887729).isSome = true := by
  decide +kernel

theorem k3137_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).1 2).2 3).1
      17069213300696518495019715779583216522223657635724166514181293000642960974828504591229617).isSome = true := by
  decide +kernel

theorem k3137_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).1 2).2 3).2
      16908871537168532247623552615912000104045746873245595205708830846593502416848386528764593).isSome = true := by
  decide +kernel

theorem k3137_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).2 2).1 3).1
      16724623604460591690715773796711709689642900734749046685083620797125687530607399459249).isSome = true := by
  decide +kernel

theorem k3137_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).2 2).1 3).2
      66297546095927717796287033116403303810222212415519348390762614185899227660385609186476).isSome = true := by
  decide +kernel

theorem k3137_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).2 2).2 3).1
      14203766814952619761211162345605009712041402100168944799351143852).isSome = true := by
  decide +kernel

theorem k3137_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).2 2).2 3).2
      195275170390248976737204994028262755421604766385).isSome = true := by
  decide +kernel

theorem k3137_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).1
      1409049081154905383249992306686222368628081043352958427084627255242214342549778301731589051809126930545518657627).isSome = true := by
  decide +kernel

theorem k3137_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).2 2).1 3).1
      17415264547756536550758347540588821780104577452601998023486582358925206023035264370).isSome = true := by
  decide +kernel

theorem k3137_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).2 2).1 3).2
      1480684293539677692652492722296145597213885918282906139665891198409406742940193703766198273818859352671692820153710135571954).isSome = true := by
  decide +kernel

theorem k3137_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).2 2).2
      23869916007221153045449367509427839678201994387561125722453695411322221997924091562351601664094075228455482091270560496225351).isSome = true := by
  decide +kernel

theorem k3137_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).1 2).1 3).1
      376120285094648272531743095163182894831603644324444968388764572917710984304899946735304498256512417317858171990251539824211186).isSome = true := by
  decide +kernel

theorem k3137_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).1 2).1 3).2
      1752074179260621811411790352396277088416868913410027351458182184563877125824472053734701674613070246411739143484500051070523527220936604734608364466).isSome = true := by
  decide +kernel

theorem k3137_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).1 2).2 3).1
      16915425188051221779233152675252231374621727190523319895205098987961653470606641522).isSome = true := by
  decide +kernel

theorem k3137_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).1 2).2 3).2
      78755654316315005060726338196610289527206164202588972366537912709178193810487801593376339750158735072690).isSome = true := by
  decide +kernel

theorem k3137_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).2 2).1 3).1
      23431405059054655610765501835135960178561401958863823335110580226813482420683554531508618430410224887984566981232315325573625522).isSome = true := by
  decide +kernel

theorem k3137_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).2 2).1 3).2
      93120559508693633160948169710619283633950323522172402931688656130552224641152182200169206350750830225380393453318202872897599154).isSome = true := by
  decide +kernel

theorem k3137_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).2 2).2 2).1
      22759704098920964058593329982514977519549625624872093587088657916338491877187194646749662892073264499750632844596822565281203).isSome = true := by
  decide +kernel

theorem k3137_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).2 2).2 2).2
      22913496985080862294864131991313039955631821354967901112859970350993372864702089716620647321397956964487893255333438419262897).isSome = true := by
  decide +kernel

theorem k3137_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).1 3).1
      7412648197132405460551608904786646259727167348043741537285231619497165962491625849114872073112800485231419204255233235784711166744912891875423686).isSome = true := by
  decide +kernel

theorem k3137_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).1 3).2 2).1
      71745275109757003254935212487473971365725480091320918825254114982534874306380837164233).isSome = true := by
  decide +kernel

theorem k3137_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).1 3).2 2).2
      17477216983457457756390766128275434111060939317425006603708966819549930225258655089).isSome = true := by
  decide +kernel

theorem k3137_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).2 3).1
      72283364970615941030482923488071486423402323554120906513070546547282808438352955974).isSome = true := by
  decide +kernel

theorem k3137_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).2 3).2
      332545498236212321958803822257627656782807830508165904603123152551883051708617129046307722895799361041650).isSome = true := by
  decide +kernel

theorem k3137_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).1 3).1 2).1
      4372650175196867890283033688367468749632849010229152755156850329493556367556041381681).isSome = true := by
  decide +kernel

theorem k3137_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).1 3).1 2).2
      949183930712676497565763311837076110880520460079356836070502784177).isSome = true := by
  decide +kernel

theorem k3137_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).1 3).2 2).1
      68697017443646913844914075115626536908326802852859691690519963158841532290110453029681).isSome = true := by
  decide +kernel

theorem k3137_47 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).1 3).2 2).2
      4321262387782621734376761557651326720677280788202394405169736431289631760344969025329).isSome = true := by
  decide +kernel

theorem k3137_48 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).2 3).1
      1538093892394330979873253076857407754407854476006640390766584778877844948004426743410606636775362164212987593254221569284769222).isSome = true := by
  decide +kernel

theorem k3137_49 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).2 3).2
      1779288366762722787104720581461381084511136238531074088359282739864376628105975287758180932908436422702396328008124358811265912954439017621692707526).isSome = true := by
  decide +kernel

theorem k3137_50 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).1 2).1 3).1
      1083415190695847677391145821024017360078881482984313738130465827241701374655473469987633).isSome = true := by
  decide +kernel

theorem k3137_51 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).1 2).1 3).2
      316784370716140651705851276196985438618592158095450298883449417870607618547717862546804894134221021070647089).isSome = true := by
  decide +kernel

theorem k3137_52 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).1 2).2 3).1
      4255964482208407731950721793794844406395589748120461044109670064613936937687809808177).isSome = true := by
  decide +kernel

theorem k3137_53 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).1 2).2 3).2
      67281403167098048113185420477328826303415032045359013512316471655251888145746513730353).isSome = true := by
  decide +kernel

theorem k3137_54 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).2 2).1 3).1
      266101037846743656256194232416014344755042001974243387864175385994643700106405568300).isSome = true := by
  decide +kernel

theorem k3137_55 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).2 2).1 3).2
      4219323240725950252770609975054413157275069574425385857105898205324571203953130100529).isSome = true := by
  decide +kernel

theorem k3137_56 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).2 2).2 3).1
      268037556847103447437913919740845232744118076725205581650855189522719914504712838956).isSome = true := by
  decide +kernel

theorem k3137_57 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).2 2).2 3).2
      66039463730444044168398021165633707546753860273325457478734573881825841598438954956).isSome = true := by
  decide +kernel

theorem k3137_58 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).1 2).1 3).1
      16973796106016083120288768783059428896070921559858594029421036487665819944362300115638473).isSome = true := by
  decide +kernel

theorem k3137_59 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).1 2).1 3).2
      262827402453618628624857689473749841593337467456648892032098768922228669712170348804273).isSome = true := by
  decide +kernel

theorem k3137_60 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).1 2).2 3).1
      66548285701841081585111106288091150597500565440495753062001299151698029032428131162929).isSome = true := by
  decide +kernel

theorem k3137_61 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).1 2).2 3).2
      65933761857492651634007660757792266109796289546745769888187585446223713711653455355441).isSome = true := by
  decide +kernel

theorem k3137_62 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).2 2).1 3).1
      66769897286718591300302982175357480986076003983702242276430472623568412202034727590705).isSome = true := by
  decide +kernel

theorem k3137_63 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).2 2).1 3).2
      16536071645354091858594933940216404579950968002830359863691992905900856997702831332913).isSome = true := by
  decide +kernel

theorem k3137_64 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).2 2).2 3).1
      4185484679820080878887802681251946699099250236808743804094856902541899506183560845105).isSome = true := by
  decide +kernel

theorem k3137_65 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).2 2).2 3).2
      4146025514812307466191113943501348701165206928537481111332474817293063026007375206193).isSome = true := by
  decide +kernel

theorem k3137_66 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).1
      29852516675050240180973878241638850578770697192352619214902681782341687794147525475320945034238143178173460424504364206436712479117117414576992717083).isSome = true := by
  decide +kernel

theorem k3137_67 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).2 2).1 3).1
      69314171495379821590003922546610047742333166821096095062117229597957597897861767750).isSome = true := by
  decide +kernel

theorem k3137_68 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).2 2).1 3).2
      80323482818233424678593897267645400661130334935900512093313603371821486787502249526258941298296873508274).isSome = true := by
  decide +kernel

theorem k3137_69 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).2 2).2
      23739708679301314368906871194280784093912161476224839675193797112830108960003768900235872566530443327250709757676454931320903).isSome = true := by
  decide +kernel

theorem k3137_70 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).1 2).1 3).1
      81358031445285393441331023741231368415449976529630788920366683887721006036225730362640651942594051462795974).isSome = true := by
  decide +kernel

theorem k3137_71 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).1 2).1 3).2
      80137554665697287930366571672903152473955237539772219419805162998843947276607462378771893188630834367265970).isSome = true := by
  decide +kernel

theorem k3137_72 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).1 2).2 3).1
      1077038661825351164120462858556943937597412160983743400109353669450588339969781074310).isSome = true := by
  decide +kernel

theorem k3137_73 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).1 2).2 3).2
      1092107927939498275058296944508250178069913657092623499324162302036176386301887649780425).isSome = true := by
  decide +kernel

theorem k3137_74 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).2 2).1 2).1
      5786488650945725906747881377935700431498315676470895251180761810635942509997622800991683305534536090386377614527746179541131059).isSome = true := by
  decide +kernel

theorem k3137_75 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).2 2).1 2).2
      23239798335493314401097046303081387363711551694085510247115366072855266983283139615856244316047430156308169614058504195621354675).isSome = true := by
  decide +kernel

theorem k3137_76 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).2 2).2 2).1
      19723687693098253366029921494182989600549497203391478251832922016200433864023631598465405045680414635809971).isSome = true := by
  decide +kernel

theorem k3137_77 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).2 2).2 2).2
      16727333298613732656147169384681680565928695854157792715760759470939095539629026645809).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3137 3138 :=
  (Cover.one (box := dirCellBox) (n := 3137)
      (.split 1 (.split 2 (.split 3 (.split 3 (.split 2 (.split 3 (.leaf _ k3137_0) (.split 2 (.leaf _ k3137_1) (.leaf _ k3137_2))) (.split 3 (.leaf _ k3137_3) (.leaf _ k3137_4))) (.split 2 (.split 3 (.split 2 (.leaf _ k3137_5) (.leaf _ k3137_6)) (.split 2 (.leaf _ k3137_7) (.leaf _ k3137_8))) (.split 3 (.leaf _ k3137_9) (.leaf _ k3137_10)))) (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3137_11) (.leaf _ k3137_12)) (.split 2 (.leaf _ k3137_13) (.leaf _ k3137_14))) (.split 3 (.split 2 (.leaf _ k3137_15) (.leaf _ k3137_16)) (.split 2 (.leaf _ k3137_17) (.leaf _ k3137_18)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3137_19) (.leaf _ k3137_20)) (.split 3 (.leaf _ k3137_21) (.leaf _ k3137_22))) (.split 2 (.split 3 (.leaf _ k3137_23) (.leaf _ k3137_24)) (.split 3 (.leaf _ k3137_25) (.leaf _ k3137_26)))))) (.split 3 (.split 3 (.leaf _ k3137_27) (.split 2 (.split 3 (.leaf _ k3137_28) (.leaf _ k3137_29)) (.leaf _ k3137_30))) (.split 3 (.split 2 (.split 3 (.leaf _ k3137_31) (.leaf _ k3137_32)) (.split 3 (.leaf _ k3137_33) (.leaf _ k3137_34))) (.split 2 (.split 3 (.leaf _ k3137_35) (.leaf _ k3137_36)) (.split 2 (.leaf _ k3137_37) (.leaf _ k3137_38)))))) (.split 2 (.split 3 (.split 3 (.split 2 (.split 3 (.leaf _ k3137_39) (.split 2 (.leaf _ k3137_40) (.leaf _ k3137_41))) (.split 3 (.leaf _ k3137_42) (.leaf _ k3137_43))) (.split 2 (.split 3 (.split 2 (.leaf _ k3137_44) (.leaf _ k3137_45)) (.split 2 (.leaf _ k3137_46) (.leaf _ k3137_47))) (.split 3 (.leaf _ k3137_48) (.leaf _ k3137_49)))) (.split 3 (.split 2 (.split 2 (.split 3 (.leaf _ k3137_50) (.leaf _ k3137_51)) (.split 3 (.leaf _ k3137_52) (.leaf _ k3137_53))) (.split 2 (.split 3 (.leaf _ k3137_54) (.leaf _ k3137_55)) (.split 3 (.leaf _ k3137_56) (.leaf _ k3137_57)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3137_58) (.leaf _ k3137_59)) (.split 3 (.leaf _ k3137_60) (.leaf _ k3137_61))) (.split 2 (.split 3 (.leaf _ k3137_62) (.leaf _ k3137_63)) (.split 3 (.leaf _ k3137_64) (.leaf _ k3137_65)))))) (.split 3 (.split 3 (.leaf _ k3137_66) (.split 2 (.split 3 (.leaf _ k3137_67) (.leaf _ k3137_68)) (.leaf _ k3137_69))) (.split 3 (.split 2 (.split 3 (.leaf _ k3137_70) (.leaf _ k3137_71)) (.split 3 (.leaf _ k3137_72) (.leaf _ k3137_73))) (.split 2 (.split 2 (.leaf _ k3137_74) (.leaf _ k3137_75)) (.split 2 (.leaf _ k3137_76) (.leaf _ k3137_77))))))))

end C4.Cert.Dir079
