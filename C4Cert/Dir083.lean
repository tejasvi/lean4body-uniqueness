module

public import C4Check

public section

/-! Cells `3137 ≤ n < 3138` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir083

theorem k3137_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).1 3).1
      72459378670979246006414532217188374323766885547820642672107213080811204703157197894).isSome = true := by
  decide +kernel

theorem k3137_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).1 3).2
      1537137269196014674955119342078005956412691382610995286501055833450085467765019454775088452734890128229213429442995481572850).isSome = true := by
  decide +kernel

theorem k3137_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).1 2).2
      7279324024559253531715529353987958052005025459441966090519761544418188082975559006164700115752190033931975703515889326224587170435249375402366411).isSome = true := by
  decide +kernel

theorem k3137_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).1 3).1
      385042982088025159447855029273156558969471133113270417613187752540980724699740074596307560011562034661526270732172694802756850).isSome = true := by
  decide +kernel

theorem k3137_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).1 3).2
      378034273322157947371929585755395025760023026792843860868834478905428630932633416244211214821883963995761135562405557054829810).isSome = true := by
  decide +kernel

theorem k3137_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).1 3).2 2).2
      2069988535157493063932377545730062663486187633508213432804487965211206532659075324536949792862148393155420707531964492812998075874784667547808125849818116521290106318).isSome = true := by
  decide +kernel

theorem k3137_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).1 2).1
      22879443525303005221285924436771122315908502021498452010819392046804860263104744675398803704848013551992461930415714656476595).isSome = true := by
  decide +kernel

theorem k3137_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).1 2).2
      1251628391159710019679916145233208928562099070111847211701000882761940897717733892144124488068579052248497).isSome = true := by
  decide +kernel

theorem k3137_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).2 2).1
      17031298366649949595187929840143437606831059415605452215584436526364900117584554183484).isSome = true := by
  decide +kernel

theorem k3137_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).1 2).2 2).2
      4892745422018536700681547723827588302707230754275193956340202075106486977120008378807257452258268720499).isSome = true := by
  decide +kernel

theorem k3137_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).1 2).1
      198150601512398856590276801887928455981328299618995).isSome = true := by
  decide +kernel

theorem k3137_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).1 2).2
      1037776824174447822484517622452064237689887543449822690884583341509879480933054543420).isSome = true := by
  decide +kernel

theorem k3137_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).2 3).1
      4190178080571155497227053747212270555074975523624593310797023335748467531778773996348).isSome = true := by
  decide +kernel

theorem k3137_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).1 3).2 3).2 2).2 3).2
      899984525949594476187705493208051440630348073533107672603837322044).isSome = true := by
  decide +kernel

theorem k3137_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).1
      117147963750194394541733050498994550146157582099659121535711442821932568562255762110782624438261472564928477928539884633986065643719210751024905499).isSome = true := by
  decide +kernel

theorem k3137_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).2 2).1
      1758611027402453676162141702152356851343041581437103786907067533197731180880143044177002057626330389035703125583043875075379630080521702474151371).isSome = true := by
  decide +kernel

theorem k3137_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).1 3).2 2).2
      17151832109896003279855909007635412323916532358468037611207670961029705291216669043).isSome = true := by
  decide +kernel

theorem k3137_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).1 2).1
      27568993341784050365428896388849424257195440270973174584809097472269237439786794515886966809932846010348117267028577662744669844527890308360029646).isSome = true := by
  decide +kernel

theorem k3137_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).1 2).2
      93141628966979943568750406725345010691066994220050727589346716775584100125188203932615618912137645522624995425599751605810418).isSome = true := by
  decide +kernel

theorem k3137_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).2 2).1
      431479163833224442324104822164350420288208270240105609108533210437895233608734457848110582192554019693243055739438899728260655453381401819885233614).isSome = true := by
  decide +kernel

theorem k3137_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).1 2).2 3).2 3).2 2).2
      366783234081862658774444067691737015312727580494756383242462537880914961173654027506559665341797295995887972668896136094381298).isSome = true := by
  decide +kernel

theorem k3137_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).1 3).1
      72144955655776161501483114172524699877906644012248828482981324902239120395073034566).isSome = true := by
  decide +kernel

theorem k3137_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).1 3).2
      83023623779879981672121316460233051520009392307072094726768137529760768117110917551783903044750139553010).isSome = true := by
  decide +kernel

theorem k3137_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).1 2).2
      7252236007090389960187498069873154203228331169740328488882896080331386404210503701563769910323578099900917396485325381773836366255750479031457227).isSome = true := by
  decide +kernel

theorem k3137_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).1 3).1
      18036218790216364166096690643825327657212160350057356230356499922922305129805567483835590).isSome = true := by
  decide +kernel

theorem k3137_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).1 3).2
      69247500302009788421400627816902944181590427433017987985628025286100998413111081458866).isSome = true := by
  decide +kernel

theorem k3137_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).1 3).2 2).2
      2064309238282090624008854953776202829448566399401007797831513932667690347174671407333425158419012733601746339475988503140824443619627285112338213573758350391636510158).isSome = true := by
  decide +kernel

theorem k3137_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).1 2).1
      67066205769238757741415659557543176116798432211560529826383746072042357222096325336243).isSome = true := by
  decide +kernel

theorem k3137_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).1 2).2
      4231215229411107067467017337377534813255008827124408128438187838727253274851823589169).isSome = true := by
  decide +kernel

theorem k3137_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).2 2).1
      4245493490425174385373653943746974488331896108646962007484696741461981761079530280753).isSome = true := by
  decide +kernel

theorem k3137_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).1 2).2 2).2
      57380636970568349755816543177238446992073026270659126243159749811).isSome = true := by
  decide +kernel

theorem k3137_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).1 2).1
      16514951703771650098989590502636410342262652197590363620149591271232037067660176258620).isSome = true := by
  decide +kernel

theorem k3137_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).1 2).2
      898177448400113191415826498273643172946294001443591543819590824620).isSome = true := by
  decide +kernel

theorem k3137_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).2 2).1
      56318452222662618206048232389851452312267948835207563683318685484).isSome = true := by
  decide +kernel

theorem k3137_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).1 3).2 3).2 2).2 2).2
      260479826970170158146775667159075616485837485289831708014568251831499992373839486764).isSome = true := by
  decide +kernel

theorem k3137_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).1
      116692356257707424235193020930157448349780645473996542550220475816870974040282373188555838279857724234629532994880053937564890513026500169332328731).isSome = true := by
  decide +kernel

theorem k3137_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).2 2).1
      7010899096578429058359891689693384072572688329192735813776980544866691423556479809523154485267777753312582685398952348106741692236758150787704267).isSome = true := by
  decide +kernel

theorem k3137_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).1 3).2 2).2
      68380750855455198400996021195188208508041148940892833271555048134433450002556248435).isSome = true := by
  decide +kernel

theorem k3137_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).1 2).1
      5170985232517162785647043177124660381753975565122971687348462054656399153875152480439003841119464836057540046).isSome = true := by
  decide +kernel

theorem k3137_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).1 2).2
      23371030303242228019099195137715171137740752830733418284879948033181619599129685543286267075879918380294078774447571177135538).isSome = true := by
  decide +kernel

theorem k3137_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).2 2).1
      1459054061822386104713751927817814891819335751734607694023651041896691704448102913934867887776696994138249030234463601857879858).isSome = true := by
  decide +kernel

theorem k3137_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3137) 1).2 2).2 3).2 3).2 2).2
      67243843426824510942355121114505636086048881610054198679412290066698818888689542061234).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3137 3138 :=
  (Cover.one (box := dirCellBox) (n := 3137)
      (.split 1 (.split 2 (.split 3 (.split 3 (.split 2 (.split 3 (.leaf _ k3137_0) (.leaf _ k3137_1)) (.leaf _ k3137_2)) (.split 2 (.split 3 (.leaf _ k3137_3) (.leaf _ k3137_4)) (.leaf _ k3137_5))) (.split 3 (.split 2 (.split 2 (.leaf _ k3137_6) (.leaf _ k3137_7)) (.split 2 (.leaf _ k3137_8) (.leaf _ k3137_9))) (.split 2 (.split 2 (.leaf _ k3137_10) (.leaf _ k3137_11)) (.split 3 (.leaf _ k3137_12) (.leaf _ k3137_13))))) (.split 3 (.split 3 (.leaf _ k3137_14) (.split 2 (.leaf _ k3137_15) (.leaf _ k3137_16))) (.split 3 (.split 2 (.leaf _ k3137_17) (.leaf _ k3137_18)) (.split 2 (.leaf _ k3137_19) (.leaf _ k3137_20))))) (.split 2 (.split 3 (.split 3 (.split 2 (.split 3 (.leaf _ k3137_21) (.leaf _ k3137_22)) (.leaf _ k3137_23)) (.split 2 (.split 3 (.leaf _ k3137_24) (.leaf _ k3137_25)) (.leaf _ k3137_26))) (.split 3 (.split 2 (.split 2 (.leaf _ k3137_27) (.leaf _ k3137_28)) (.split 2 (.leaf _ k3137_29) (.leaf _ k3137_30))) (.split 2 (.split 2 (.leaf _ k3137_31) (.leaf _ k3137_32)) (.split 2 (.leaf _ k3137_33) (.leaf _ k3137_34))))) (.split 3 (.split 3 (.leaf _ k3137_35) (.split 2 (.leaf _ k3137_36) (.leaf _ k3137_37))) (.split 3 (.split 2 (.leaf _ k3137_38) (.leaf _ k3137_39)) (.split 2 (.leaf _ k3137_40) (.leaf _ k3137_41)))))))

end C4.Cert.Dir083
