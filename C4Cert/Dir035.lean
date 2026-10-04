module

public import C4Check

public section

/-! Cells `2355 ≤ n < 2356` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir035

theorem k2355_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).1 1).1
      25527284211082993091103374536128808816686183979630267157839373470305241813904643959876946753244910407836164217359567196849046573614471612409842247).isSome = true := by
  decide +kernel

theorem k2355_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).1 1).2 3).1
      63547586654358611157248358460576313271456141728877626453139352933123774975102919644977).isSome = true := by
  decide +kernel

theorem k2355_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).1 1).2 3).2
      3972972887690864877951226810374862453528137537310268184486519064831031823109917218609).isSome = true := by
  decide +kernel

theorem k2355_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).2 3).1 1).1
      211100695021658796635143331707109276389715186678245184518027153).isSome = true := by
  decide +kernel

theorem k2355_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).2 3).1 1).2
      255060482831318163671732255080148470613056281706271185523216327755482288224691265428657).isSome = true := by
  decide +kernel

theorem k2355_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).2 3).2 1).1
      15548102691008920951272522410562994737027911243043476817176496383133276264329297266).isSome = true := by
  decide +kernel

theorem k2355_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).1 2).2 3).2 1).2
      15892112149210230227737419140470225397628909860222237159083290454196265272812630644529).isSome = true := by
  decide +kernel

theorem k2355_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).1 1).1
      1877666243109005197069557808626703777564878217632914288416879367071113439490506137401831633829353695168385415477219380402669609448789254900717051947941630493376497099).isSome = true := by
  decide +kernel

theorem k2355_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).1 1).2 3).1
      989753206287312988367750985990435485860488212079850848888875750002862287311090308577).isSome = true := by
  decide +kernel

theorem k2355_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).1 1).2 3).2
      13392863460571643607020087297524532404029759209573020340772621260).isSome = true := by
  decide +kernel

theorem k2355_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).2 1).1 3).1
      62012413742201420112956430141396290458330775466830493637345361852810855729215936881).isSome = true := by
  decide +kernel

theorem k2355_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).2 1).1 3).2
      61901766909445790536315785360943304191032039241411851897052960112422842787183810929).isSome = true := by
  decide +kernel

theorem k2355_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).2 1).2 3).1
      3977356852189145154004953231539880747626794129483294918176174875488215086259746002737).isSome = true := by
  decide +kernel

theorem k2355_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).1 3).2 2).2 1).2 3).2
      247503479062334636183544832782717818643420858535171685060239819608028215768000191436).isSome = true := by
  decide +kernel

theorem k2355_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).1 3).1 1).1
      63122799437961663010230880213642124896676202031915964802184252951379177677701419754887).isSome = true := by
  decide +kernel

theorem k2355_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).1 3).1 1).2
      21986943126034976039129211767130189025741440588261117774315173595263687199131942213897113598116785630495116615248110223294418739).isSome = true := by
  decide +kernel

theorem k2355_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).1 3).2 1).1
      3944228147435404782092572207578560855364452193456919467331241290553529578006896990002).isSome = true := by
  decide +kernel

theorem k2355_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).1 3).2 1).2
      3937143497104332848114865356497113498193075563837250003615894828751907959169443075889).isSome = true := by
  decide +kernel

theorem k2355_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).2 3).1 1).1
      408369551315134481304413778966341152728549751047380410972062723260107151688767222858287051601985639756127983352861579732915456741383673037803640269).isSome = true := by
  decide +kernel

theorem k2355_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).2 3).1 1).2
      88050846357198616498415368035684213693244615343859298872918086063212213365225536258147697528300345928999686857262115933023711027).isSome = true := by
  decide +kernel

theorem k2355_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).2 3).2 1).1
      63059797541353039592537232327722580397150053905685070141749781566420031856625463628167).isSome = true := by
  decide +kernel

theorem k2355_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).1 3).2 2).2 3).2 1).2
      5492849747633013430785766574268944785762879547533025737613254817575817212579409471846932666892619037988758803431325849344138033).isSome = true := by
  decide +kernel

theorem k2355_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).1 3).1 1).1
      211650855845009042282971987594774052360580886148863575031333713).isSome = true := by
  decide +kernel

theorem k2355_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).1 3).1 1).2
      1023980593420246897227330200595623820229207337992696867296449808868004826010800950702769).isSome = true := by
  decide +kernel

theorem k2355_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).1 3).2 1).1
      15584510313391285581909932100068555278284840493854256119986137922904815614184440178).isSome = true := by
  decide +kernel

theorem k2355_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).1 3).2 1).2
      63714573610915353742172804204141135299640750046849257674017757239052662826188176121009).isSome = true := by
  decide +kernel

theorem k2355_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).2 3).1 1).1
      53028906887277923349347704708039923895149425919363234006291089).isSome = true := by
  decide +kernel

theorem k2355_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).2 3).1 1).2
      256139628050756961943462971672617522690862043347109174385654430329691482865982896105185).isSome = true := by
  decide +kernel

theorem k2355_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).2 3).2 1).1
      211518179469106276915917043527552776102028742829993385066704721).isSome = true := by
  decide +kernel

theorem k2355_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).1 2).2 3).2 1).2
      63923264796098083142723713962917117909961927926048873737646818239457502250463966160609).isSome = true := by
  decide +kernel

theorem k2355_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).1 3).1 1).1
      62143029056558895621159117996960060364726631690030952300783792303061739793187950961).isSome = true := by
  decide +kernel

theorem k2355_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).1 3).1 1).2
      15893536486028107307149905380327239156450452970861729027522622253845285499727737788209).isSome = true := by
  decide +kernel

theorem k2355_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).1 3).2 1).1
      62018625524299572809643288307410769869473892142666232788757348665606170561960384881).isSome = true := by
  decide +kernel

theorem k2355_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).1 3).2 1).2
      3977728982643025848397008012511928594253937657689604292187155033318225915698515203889).isSome = true := by
  decide +kernel

theorem k2355_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).2 3).1 1).1
      62275986757772830436830269857970860465805219088188375642601407926053851234747738481).isSome = true := by
  decide +kernel

theorem k2355_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).2 3).1 1).2
      15958207120553896247946527182425597952758855192774214153890603404684689119205542878385).isSome = true := by
  decide +kernel

theorem k2355_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).2 3).2 1).1
      62139996072858844883141266059976083782399904286322805195566756658359364370914351473).isSome = true := by
  decide +kernel

theorem k2355_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).1 3).2 2).2 3).2 1).2
      13466999906326167008001246820012712470727204806121397153141714732).isSome = true := by
  decide +kernel

theorem k2355_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).1 2).1 1).1
      6509259954978388268736541774816292731141082078805608075181580371524799392486305767175487673314841738161933420194514384076959639853102809011647227335).isSome = true := by
  decide +kernel

theorem k2355_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).1 2).1 1).2
      6505387716256598791566578509134033913925005567435598628781503212864708818397032507124867683575995041496120889184793335540306816933790188032612589363).isSome = true := by
  decide +kernel

theorem k2355_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).1 2).2 1).1
      6519881517353713165646706830675230149866957381844743265880923426657408271905849086277562594515803848385073025080081725958521097766161175824371209671).isSome = true := by
  decide +kernel

theorem k2355_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).1 2).2 1).2
      22083423062675699526808159021909831281133647644616976830258660125938899245454217448776107194105930917115261199807479294518197427).isSome = true := by
  decide +kernel

theorem k2355_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).2 2).1 1).1
      298237758913844172059100154027732886445199586417244762521573549385005035582679564066569778099937501274866893).isSome = true := by
  decide +kernel

theorem k2355_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).2 2).1 1).2
      5499514736321151925075908034699407167770437494426203129171816073120741534577266757867100427144209315646390407295442093454252849).isSome = true := by
  decide +kernel

theorem k2355_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).2 2).2 1).1
      88094460598301873092903005088254627025733229945252027640257193105852340905088509164387153687164105402731551329249520738672153799).isSome = true := by
  decide +kernel

theorem k2355_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2355) 2).2 3).2 3).2 2).2 1).2
      16173963061003783974176622315715935896626117579044446708178978632204955504366162441482035).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2355 2356 :=
  (Cover.one (box := dirCellBox) (n := 2355)
      (.split 2 (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2355_0) (.split 3 (.leaf _ k2355_1) (.leaf _ k2355_2))) (.split 3 (.split 1 (.leaf _ k2355_3) (.leaf _ k2355_4)) (.split 1 (.leaf _ k2355_5) (.leaf _ k2355_6)))) (.split 2 (.split 1 (.leaf _ k2355_7) (.split 3 (.leaf _ k2355_8) (.leaf _ k2355_9))) (.split 1 (.split 3 (.leaf _ k2355_10) (.leaf _ k2355_11)) (.split 3 (.leaf _ k2355_12) (.leaf _ k2355_13))))) (.split 2 (.split 3 (.split 1 (.leaf _ k2355_14) (.leaf _ k2355_15)) (.split 1 (.leaf _ k2355_16) (.leaf _ k2355_17))) (.split 3 (.split 1 (.leaf _ k2355_18) (.leaf _ k2355_19)) (.split 1 (.leaf _ k2355_20) (.leaf _ k2355_21))))) (.split 3 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2355_22) (.leaf _ k2355_23)) (.split 1 (.leaf _ k2355_24) (.leaf _ k2355_25))) (.split 3 (.split 1 (.leaf _ k2355_26) (.leaf _ k2355_27)) (.split 1 (.leaf _ k2355_28) (.leaf _ k2355_29)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2355_30) (.leaf _ k2355_31)) (.split 1 (.leaf _ k2355_32) (.leaf _ k2355_33))) (.split 3 (.split 1 (.leaf _ k2355_34) (.leaf _ k2355_35)) (.split 1 (.leaf _ k2355_36) (.leaf _ k2355_37))))) (.split 3 (.split 2 (.split 1 (.leaf _ k2355_38) (.leaf _ k2355_39)) (.split 1 (.leaf _ k2355_40) (.leaf _ k2355_41))) (.split 2 (.split 1 (.leaf _ k2355_42) (.leaf _ k2355_43)) (.split 1 (.leaf _ k2355_44) (.leaf _ k2355_45)))))))

end C4.Cert.Dir035
