module

public import C4Check

public section

/-! Cells `3489 ≤ n < 3530` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir103

theorem c0 : allCells dirCell 3489 3507 [
    147549821573607769844, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 597387598098022343058,
    3916232685194232077599879474207708227193151516779329047349882757620685619178262699079] = true := by
  decide +kernel

theorem c1 : allCells dirCell 3507 3508 [
    211989530135179421913920010866900202283385863435478800857044704050] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3508 3509 [
    243978744349028787404977143835266456647098113334679430536391049130024104667082479410] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3509 3510 [
    975077171423765276181955720879669805918449871916956869213293124071905713262425693362] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3510 3512 [
    3896263255664148077385548724953280106263507429151687458692151102074427778778098922162,
    206100021946559724102461528052483668396084608896072719170545074] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3512 3514 [
    51492751364279523107673904157666087248363620578058207581268338,
    51467713787366276285454357621859378928224739736079415008416114] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3514 3516 [
    51448342900058283046443345311567737908411310090453033861984626,
    51433429180249919710042199396311063713160134415190970480719218] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3516 3528 [
    51424498730101454925387913966772991233267847351714628554268561, 147549214368321307716, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3528_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3528) 1).1 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k3528_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3528) 1).1 2).1 3).2 3).1
      1).isSome = true := by
  decide +kernel

theorem k3528_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3528) 1).1 2).1 3).2 3).2 3).1
      42809193684634322977466001134518197250840904501597547506274357530).isSome = true := by
  decide +kernel

theorem k3528_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3528) 1).1 2).1 3).2 3).2 3).2
      1943841199001754302090751901925639084404005339515928414593044436444613684282464324987026444266730348234786351205379129664915517328991104076620797722).isSome = true := by
  decide +kernel

theorem k3528_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3528) 1).1 2).2
      1).isSome = true := by
  decide +kernel

theorem k3528_5 : (checkBoxH dirMode depth (splitBox (dirCellBox 3528) 1).2
      28592229789995549134).isSome = true := by
  decide +kernel

theorem k3529_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).1 3).1
      14600240737860605026867942506916245924146953633981242766276356616170578547528553158616725898934132438292249).isSome = true := by
  decide +kernel

theorem k3529_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).1 3).2
      3136983049513838234631582173747636639066706308695707560033119979639633187973651260790553).isSome = true := by
  decide +kernel

theorem k3529_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).2 1).1 3).1
      71800706566031484196990247037939288224875400458394235467066797611473089397539195206).isSome = true := by
  decide +kernel

theorem k3529_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).2 1).1 3).2
      17902045983558518288161747805379915574225306660283175856080228342994313346505091060422).isSome = true := by
  decide +kernel

theorem k3529_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).2 1).2
      6).isSome = true := by
  decide +kernel

theorem k3529_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).1 3).1
      3112235549663637438388461254383759177209460213344243267865704380460256754784602333582489).isSome = true := by
  decide +kernel

theorem k3529_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).1 3).2
      1301316714896649747616042223502957990448041488637924163658368804073441249993461521798861150325439947052266646).isSome = true := by
  decide +kernel

theorem k3529_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).2 1).1 3).1
      17546083102762765090885496303183978319791710838095402726923921137718650221512808879302).isSome = true := by
  decide +kernel

theorem k3529_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).2 1).1 3).2
      68870614246653939651073290428066170937553922223680090758250193658687256302404785734854).isSome = true := by
  decide +kernel

theorem k3529_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).2 1).2
      6).isSome = true := by
  decide +kernel

theorem k3529_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).1 3).1
      344924902328901663020850366274365220291508619366023339282451557528294604084590001228906585983959034323980566).isSome = true := by
  decide +kernel

theorem k3529_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).1 3).2 2).1
      24310351356669298741281088418907999516717074291864207385086730662875115103047644145977411913048463913065729715560107305326021).isSome = true := by
  decide +kernel

theorem k3529_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).1 3).2 2).2
      10828302573516554065389890311443579225937004687848741036112915525).isSome = true := by
  decide +kernel

theorem k3529_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).1 1).1 3).1
      68917390395567605217622351827802044934709657785854065403709926118294673047528691270).isSome = true := by
  decide +kernel

theorem k3529_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).1 1).1 3).2
      69693372273685804087728978373212705409358876849222094639881943420951897198020567981234).isSome = true := by
  decide +kernel

theorem k3529_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).1 1).2
      209453734741269532827023980728139581463193936216107).isSome = true := by
  decide +kernel

theorem k3529_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).2 1).1
      6969017777073323675341505562453410603007912147737493809481397055260973544656710518882967403685394165124489193652906439632630324454831509077824971).isSome = true := by
  decide +kernel

theorem k3529_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).2 1).2
      52208313682143516835040254725362453929198994106413437110590370863655381643004930270225863).isSome = true := by
  decide +kernel

theorem k3529_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).1 3).1 2).1
      68620134439766019890194848416703691552075736551760024374858668451022363852936721062323351).isSome = true := by
  decide +kernel

theorem k3529_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).1 3).1 2).2
      1460626956493330677371268701312521649251862756952330413050399156995462688491112062241019102830219621127613522004851119700925981).isSome = true := by
  decide +kernel

theorem k3529_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).1 3).2 2).1
      16822424661169719314592971279658186047623292005214427191264388595158010500034717038155863).isSome = true := by
  decide +kernel

theorem k3529_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).1 3).2 2).2
      22933540736037243715700700288502632797834501462281480468084499374034713153294301670158630817666952229411121925779946132089888279).isSome = true := by
  decide +kernel

theorem k3529_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).1 1).1 2).1
      93907252343745288771814110167848426755237374491964263754008708363977071298107543346474886162577399859068230311348219852776183687).isSome = true := by
  decide +kernel

theorem k3529_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).1 1).1 2).2
      79541145117186308363225977360231683446348239766122295536111669841109122271862086617613461449337543311680711).isSome = true := by
  decide +kernel

theorem k3529_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).1 1).2
      6).isSome = true := by
  decide +kernel

theorem k3529_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).2 2).1
      66328277535111141769605807878195782188463235019685104099321458285987009865885523659404372520014086570908544343922019832230796829).isSome = true := by
  decide +kernel

theorem k3529_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).2 2).2
      23050102174198655069305041865669594312662195525477417891347210787781908892376546693063290666589507831273965522563634194874326557).isSome = true := by
  decide +kernel

theorem k3529_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).1 1).1 3).1
      17173040483548865885231343766067288109848502007949001975619121601500365688909906926770).isSome = true := by
  decide +kernel

theorem k3529_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).1 1).1 3).2
      67610114908177278441088125776638204694965346455353409176901992953034968028547548161222).isSome = true := by
  decide +kernel

theorem k3529_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).1 1).2
      204039161108442076055194145719746535763567388672043).isSome = true := by
  decide +kernel

theorem k3529_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).2 1).1 2).1
      4252153643344132078319704973481332902420264011904601034303361069506958928569313302321).isSome = true := by
  decide +kernel

theorem k3529_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).2 1).1 2).2
      266185031891138659667371882653827943870787149091964070363085073024939272788838837619).isSome = true := by
  decide +kernel

theorem k3529_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).2 1).2
      4458713630999208946032337785407066388121306838457836094561930164408759871655016055761847579).isSome = true := by
  decide +kernel

theorem k3529_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).1 1).1 2).1
      5782750937551912471832235902777679286652341209570290012213196113029781319350151749314169581643797545451351742403154252419028871).isSome = true := by
  decide +kernel

theorem k3529_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).1 1).1 2).2
      78552169517572373018454804353272642834650618257480224827600263167599350928998351612247170684180354735703687).isSome = true := by
  decide +kernel

theorem k3529_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).1 1).2
      48838984846983826041717243077549990169134002186).isSome = true := by
  decide +kernel

theorem k3529_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).2 1).1 2).1
      4153974630889203579744110387249195878172219620150370237296934484695349960771644462899).isSome = true := by
  decide +kernel

theorem k3529_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).2 1).1 2).2
      4168940215651697272578710258729403806104764816976740901345889283239211922466110805811).isSome = true := by
  decide +kernel

theorem k3529_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).2 1).2
      266932133248288679963101603243395528479966096471499332821390304929797147787308380114214).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3489 3530 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 3528)
      (.split 1 (.split 2 (.split 3 (.leaf _ k3528_0) (.split 3 (.leaf _ k3528_1) (.split 3 (.leaf _ k3528_2) (.leaf _ k3528_3)))) (.leaf _ k3528_4)) (.leaf _ k3528_5))).trans <|
  (Cover.one (box := dirCellBox) (n := 3529)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3529_0) (.leaf _ k3529_1)) (.split 1 (.split 3 (.leaf _ k3529_2) (.leaf _ k3529_3)) (.leaf _ k3529_4))) (.split 2 (.split 3 (.leaf _ k3529_5) (.leaf _ k3529_6)) (.split 1 (.split 3 (.leaf _ k3529_7) (.leaf _ k3529_8)) (.leaf _ k3529_9)))) (.split 3 (.split 3 (.leaf _ k3529_10) (.split 2 (.leaf _ k3529_11) (.leaf _ k3529_12))) (.split 2 (.split 1 (.split 3 (.leaf _ k3529_13) (.leaf _ k3529_14)) (.leaf _ k3529_15)) (.split 1 (.leaf _ k3529_16) (.leaf _ k3529_17))))) (.split 2 (.split 2 (.split 3 (.split 2 (.leaf _ k3529_18) (.leaf _ k3529_19)) (.split 2 (.leaf _ k3529_20) (.leaf _ k3529_21))) (.split 3 (.split 1 (.split 2 (.leaf _ k3529_22) (.leaf _ k3529_23)) (.leaf _ k3529_24)) (.split 2 (.leaf _ k3529_25) (.leaf _ k3529_26)))) (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k3529_27) (.leaf _ k3529_28)) (.leaf _ k3529_29)) (.split 1 (.split 2 (.leaf _ k3529_30) (.leaf _ k3529_31)) (.leaf _ k3529_32))) (.split 2 (.split 1 (.split 2 (.leaf _ k3529_33) (.leaf _ k3529_34)) (.leaf _ k3529_35)) (.split 1 (.split 2 (.leaf _ k3529_36) (.leaf _ k3529_37)) (.leaf _ k3529_38)))))))

end C4.Cert.Dir103
