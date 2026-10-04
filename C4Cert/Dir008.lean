module

public import C4Check

public section

/-! Cells `1298 ≤ n < 1353` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir008

theorem k1298_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1298) 3).1 2).1
      3983016508820440213093828585049060695318145371863025831189053098721184832010303120962353).isSome = true := by
  decide +kernel

theorem k1298_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1298) 3).1 2).2
      3983249593666498271013356196693229881132007417395378511076749713505360379369745017064241).isSome = true := by
  decide +kernel

theorem k1298_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1298) 3).2 2).1
      62207014915946493461074155595241422513446899769729365706065024538983451195402443872049).isSome = true := by
  decide +kernel

theorem k1298_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1298) 3).2 2).2
      995325609399789940101390552916948568008930406958807287607132274973996466818348923950897).isSome = true := by
  decide +kernel

theorem k1299_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1299) 3).1 2).1
      242947380025578584409297643878847275304136852324852510121404313021732765470831942001).isSome = true := by
  decide +kernel

theorem k1299_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1299) 3).1 2).2
      242945600174643240635233750534439231994384275833581418671002906635583310531853375857).isSome = true := by
  decide +kernel

theorem k1299_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1299) 3).2
      17921475286420367058324255072355451183902314262373832481821998733782652134747545948678622337340978532497).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 1300 1322 [
    44581836982188906513281918593981118804581638, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 51] = true := by
  decide +kernel

theorem k1322_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1322) 3).1
      15700980241249787697731436207775760638023115219868387091687129963712790115264912463046).isSome = true := by
  decide +kernel

theorem k1322_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1322) 3).2 2).1
      289038796344704114386034636565466577066900140920866254954706782240927249688203841282418058285689891021169).isSome = true := by
  decide +kernel

theorem k1322_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1322) 3).2 2).2
      72272489910565879401201228459148239434048112055253667118586491108576252916231982803826156577226672371057).isSome = true := by
  decide +kernel

theorem k1323_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1323) 3).1 2).1
      1608821122841131514140930641188266004451561550847491345100925261365626824138099740336793727742806816313557253350252467882255260985559644497161606065).isSome = true := by
  decide +kernel

theorem k1323_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1323) 3).1 2).2
      1362904361454721228471033749105334375255995884834401437181085577967125809561395468391369376988866173949451436974361760742585165).isSome = true := by
  decide +kernel

theorem k1323_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1323) 3).2 2).1
      1608121693449132040857435958016294070688454580668993579674370998834615026234356687799678155381309684334000513634252059988143152641144193226712244017).isSome = true := by
  decide +kernel

theorem k1323_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1323) 3).2 2).2
      87102681887747789658960038042161380898497665174953788425828860814409486941121739118322567390893478488961710158663231708520086705).isSome = true := by
  decide +kernel

theorem k1324_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1324) 3).1 2).1
      87003542092657777551353620492726367573333036016072741506262248587316234233975313954269782230106969994913667308809578073776672561).isSome = true := by
  decide +kernel

theorem k1324_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1324) 3).1 2).2
      5438557636363837828316932923995505970999674241232123068308447477060550574418546678857589355564745227839837516144863389482867505).isSome = true := by
  decide +kernel

theorem k1324_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1324) 3).2 2).1
      4711960779110572618251559211401021732026640532898856649686579598084044100595176881975060854110111671192505137).isSome = true := by
  decide +kernel

theorem k1324_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1324) 3).2 2).2
      294497971517422758947922615569862457608732662341350359191042097241883461391810584052474148088529109064735537).isSome = true := by
  decide +kernel

theorem k1325_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1325) 3).1 2).1
      347815544937719086846300516653683773333698279391178282196960418469775150691554619329454579569871943935731258721230593219181802289).isSome = true := by
  decide +kernel

theorem k1325_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1325) 3).1 2).2
      3988432981154231258351196912681254139929897007461859582096697521018375950649077032383281).isSome = true := by
  decide +kernel

theorem k1325_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1325) 3).2 2).1
      3985578580171100676266593556096310949141605511261301722694160690002155343774669245346609).isSome = true := by
  decide +kernel

theorem k1325_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1325) 3).2 2).2
      996462222695915532935625300711801145899569627115096495431131754532608598587661527642929).isSome = true := by
  decide +kernel

theorem k1326_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1326) 3).1 2).1
      63733404524417150270614048395152045480280349009645628916971364857448942454668310274985165).isSome = true := by
  decide +kernel

theorem k1326_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1326) 3).1 2).2
      995855215089837640179412423146088573282887843814420323256159295302362925319132410108721).isSome = true := by
  decide +kernel

theorem k1326_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1326) 3).2 1).1
      3887436896909742487108895863175003486501552224414516818192228712827552121057890326322).isSome = true := by
  decide +kernel

theorem k1326_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1326) 3).2 1).2
      15556254878706650173005447607884600217722977122420811481025325898472348293242044242738).isSome = true := by
  decide +kernel

theorem k1327_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1327) 3).1
      400172311170161877181447281446766406762171766550084254722183611023135047141429402154033358495483155812605123731587764852181282458174185382869978413).isSome = true := by
  decide +kernel

theorem k1327_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1327) 3).2
      60724052609669631296166991626679976833301761071687605884108778335764104234883453713).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 1328 1350 [
    44580481045051056148339633058364878255732998, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 51] = true := by
  decide +kernel

theorem k1350_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1350) 3).1
      3925999433110673181992282940823994115205935233464138805651420348723331929724877559558).isSome = true := by
  decide +kernel

theorem k1350_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1350) 3).2
      29737679048537440412206741404372217714652769943365660128832777510503140680771905078812358877779254602411689595270329832610982868196040832189828051704688822962292143558).isSome = true := by
  decide +kernel

theorem k1351_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1351) 3).1 2).1
      21301840123976133039392563903620747461606491487794053757238609025625709962425751647187011445770719836519001045120030141632845).isSome = true := by
  decide +kernel

theorem k1351_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1351) 3).1 2).2
      18044107249997351594473719460500213371365901325383623022036536241438528286575430035874828559469148914033).isSome = true := by
  decide +kernel

theorem k1351_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1351) 3).2 2).1
      4612595294703313632544977559178924494179868324102753709559417302166175047998478810623035440831336065686705).isSome = true := by
  decide +kernel

theorem k1351_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1351) 3).2 2).2
      62569873859836912237616010386846242796413915967143793983398185067217503695265088232625).isSome = true := by
  decide +kernel

theorem k1352_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1352) 3).1 2).1
      18427940370853118706973923659109951246360110857658030309545241847762326358881325578875729079008845039819569).isSome = true := by
  decide +kernel

theorem k1352_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1352) 3).1 2).2
      4607240300445364225636004740272617282039250556404756846696889783779599591450136882488113100287042597803825).isSome = true := by
  decide +kernel

theorem k1352_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1352) 3).2 2).1
      1178081437582827150401540011894216129840141462903626529935553148613847521576644975384754816269167902482357041).isSome = true := by
  decide +kernel

theorem k1352_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1352) 3).2 2).2
      5439306503961126496894209121302504535953219041357787955913024067135289158025958158489742282376992500130213803035163782880750652).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1298 1353 :=
  (Cover.one (box := dirCellBox) (n := 1298)
      (.split 3 (.split 2 (.leaf _ k1298_0) (.leaf _ k1298_1)) (.split 2 (.leaf _ k1298_2) (.leaf _ k1298_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1299)
      (.split 3 (.split 2 (.leaf _ k1299_0) (.leaf _ k1299_1)) (.leaf _ k1299_2))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 1322)
      (.split 3 (.leaf _ k1322_0) (.split 2 (.leaf _ k1322_1) (.leaf _ k1322_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1323)
      (.split 3 (.split 2 (.leaf _ k1323_0) (.leaf _ k1323_1)) (.split 2 (.leaf _ k1323_2) (.leaf _ k1323_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1324)
      (.split 3 (.split 2 (.leaf _ k1324_0) (.leaf _ k1324_1)) (.split 2 (.leaf _ k1324_2) (.leaf _ k1324_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1325)
      (.split 3 (.split 2 (.leaf _ k1325_0) (.leaf _ k1325_1)) (.split 2 (.leaf _ k1325_2) (.leaf _ k1325_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1326)
      (.split 3 (.split 2 (.leaf _ k1326_0) (.leaf _ k1326_1)) (.split 1 (.leaf _ k1326_2) (.leaf _ k1326_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1327)
      (.split 3 (.leaf _ k1327_0) (.leaf _ k1327_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 1350)
      (.split 3 (.leaf _ k1350_0) (.leaf _ k1350_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1351)
      (.split 3 (.split 2 (.leaf _ k1351_0) (.leaf _ k1351_1)) (.split 2 (.leaf _ k1351_2) (.leaf _ k1351_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1352)
      (.split 3 (.split 2 (.leaf _ k1352_0) (.leaf _ k1352_1)) (.split 2 (.leaf _ k1352_2) (.leaf _ k1352_3))))

end C4.Cert.Dir008
