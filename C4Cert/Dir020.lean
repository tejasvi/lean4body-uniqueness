module

public import C4Check

public section

/-! Cells `1940 ≤ n < 1966` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir020

theorem c0 : allCells dirCell 1940 1941 [
    3995390220081470029597228682284365002591433574068551103112390057212525334681510174081998] = true := by
  decide +kernel

theorem c1 : allCells dirCell 1941 1942 [
    287441458781903976522608908013446018758117218108852337026948694574301292607463046744366033913885635236594] = true := by
  decide +kernel

theorem c2 : allCells dirCell 1942 1943 [
    287121042704126599930377282455132357386159880783697550158302342111160302832000147451981022287906837222130] = true := by
  decide +kernel

theorem c3 : allCells dirCell 1943 1945 [
    62215293066279234247787015275558212756915453273256532847106921385534677709522383688433,
    51429420267695432473860154145933767528449926718197287177251985] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1945 1963 [
    147499598218923730996, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k1963_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1963) 3).1
      18782915920946502294011900273347689426096281084563124727460184008205520327575084121051747260427939917918522).isSome = true := by
  decide +kernel

theorem k1963_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1963) 3).2 2).1 2).1
      25956323535129969128841620566762578237109521833725060300571163390348537265494378616164023789185520614861631022115055132887986148617384722288739041735).isSome = true := by
  decide +kernel

theorem k1963_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1963) 3).2 2).1 2).2
      5760307050880991915997112842546894972186591110400388342094776778053596315068567970668626130041421554392553609069734847093895868400071).isSome = true := by
  decide +kernel

theorem k1963_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1963) 3).2 2).2 3).1
      1063831068136953667842658232473677470167551705277598141745459178954606115471808780787118457286).isSome = true := by
  decide +kernel

theorem k1963_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1963) 3).2 2).2 3).2 2).1
      63134302977042393604865534123237209285116164137186795304338785706105138411724680688785).isSome = true := by
  decide +kernel

theorem k1963_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1963) 3).2 2).2 3).2 2).2
      63216359417561302111191224766845521668839350607518415501936686446748237551683772863633).isSome = true := by
  decide +kernel

theorem k1964_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).1 2).1 3).1
      1161324319376127200273624710521457206381162485817377146370495665895597751553076433870356516205729581523205).isSome = true := by
  decide +kernel

theorem k1964_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).1 2).1 3).2
      4638517470950301342984403783206109976742724506696057120127741375047376465850215837779566931970362266190669).isSome = true := by
  decide +kernel

theorem k1964_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).1 2).2 3).1
      18589037478296482973252168338581748318244192519029433566347634944229270698299810425565329113213226600363269).isSome = true := by
  decide +kernel

theorem k1964_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).1 2).2 3).2
      85607299959412330830433637649519914630141785968231074087353579274535499269646849464170958598930509597558395671471192749617741).isSome = true := by
  decide +kernel

theorem k1964_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).2 2).1 3).1
      3935261088626145568918877466755351822185487912186316249988409281462873458106969334597).isSome = true := by
  decide +kernel

theorem k1964_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).2 2).1 3).2
      15679026647027174606088590243714595654542708179026243107828656537027004775292257655985).isSome = true := by
  decide +kernel

theorem k1964_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).2 2).2 3).1
      296572592358972922733034568933973397220466207552758903340109655219813461675084176930696897998078753610579525).isSome = true := by
  decide +kernel

theorem k1964_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).2 2).2 3).2
      15722820872520190652210786043893055008708968112626791219550779419870006981995292394885).isSome = true := by
  decide +kernel

theorem k1964_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).1 3).1 2).1
      5491617479841931955101687110352409850197863964894586236998799625461589447584438903578966492513284784326267917522379575423899397).isSome = true := by
  decide +kernel

theorem k1964_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).1 3).1 2).2
      21990258613989507852277256527914946552185624832466710520919320214035254268527437497113835370723489632594961337668103021982750469).isSome = true := by
  decide +kernel

theorem k1964_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).1 3).2 2).1
      404513944336958961281745551608076725050876226281027935388347119214076837435119670780439320682683168331499158933003077146562808961872963025874467397).isSome = true := by
  decide +kernel

theorem k1964_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).1 3).2 2).2
      1619439839792110371471355516674052323430485829539289749140689619960190358296452252596931630814865685212143063658737366613246338779075223129213773125).isSome = true := by
  decide +kernel

theorem k1964_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).2 3).1 2).1
      1368805899991657146081444080190271987527942089706795512164142137439056911682156923312323999866895638991838737440875742228609861).isSome = true := by
  decide +kernel

theorem k1964_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).2 3).1 2).2
      7464821863995904573985388520027493096444239326923436762515749581531916582200137900836835873967774879156904473117066002242919707975584186655915789528463370040202175949).isSome = true := by
  decide +kernel

theorem k1964_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).2 3).2 2).1
      341726800447732089486168812091842436094324936753461207464111049083509342386139047280015617953744789352791486941294447855033777).isSome = true := by
  decide +kernel

theorem k1964_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).2 3).2 2).2
      87522971459228457042971120213165624359259379324602725431620712420186406454193700298229341071076611065343025441468069719621117389).isSome = true := by
  decide +kernel

theorem k1965_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).1 2).1 1).1
      978722031819889877853996341025513614504532669058926174343085112737658278336092986547).isSome = true := by
  decide +kernel

theorem k1965_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).1 2).1 1).2
      15289666804664057047823361736229875612003335581010525031781499676950991594631450995).isSome = true := by
  decide +kernel

theorem k1965_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).1 2).2 1).1
      3914621633604061354202930335431063486524999009598720685565222222208421156664887547699).isSome = true := by
  decide +kernel

theorem k1965_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).1 2).2 1).2
      3913905557233314590174592535972168206554214668285818077129190009194003516515799193395).isSome = true := by
  decide +kernel

theorem k1965_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).2 2).1
      72120164930753559249342564178499190900097129497032819725281590754354333574899552174722710158595129345485).isSome = true := by
  decide +kernel

theorem k1965_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).2 2).2
      100536084520016141946354504315226855474220389915796900361662450294132156725618450903498922443956633870304420174490591367073653489929546554463085773).isSome = true := by
  decide +kernel

theorem k1965_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).1 2).1 1).1
      3915924448406480242000073951095136587271164152683089486213611673007829857746131162931).isSome = true := by
  decide +kernel

theorem k1965_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).1 2).1 1).2
      15660749604003220484258090099558413140341190859366130227792346480601974415903246015283).isSome = true := by
  decide +kernel

theorem k1965_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).1 2).2 3).1
      4628394733655639870790430891910540323756195953251315694885162077566736915438542616830944279310138333992753).isSome = true := by
  decide +kernel

theorem k1965_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).1 2).2 3).2
      250580183060162609259313602849501433945729843590172215879973338249697425429687841347377).isSome = true := by
  decide +kernel

theorem k1965_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).2 2).1
      411639032075353344965103711532946717403825014397586426224429541874107212588261261387243766375458684233722494282837902974725971758901537315429260025029).isSome = true := by
  decide +kernel

theorem k1965_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).2 2).2 1).1
      3911177014366765547977280178946600455261591993054257456838051115224460871657409632051).isSome = true := by
  decide +kernel

theorem k1965_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).2 2).2 1).2
      3910350674978557757947126136702957367054150573283757523896750788719909537964382279475).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1940 1966 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1963)
      (.split 3 (.leaf _ k1963_0) (.split 2 (.split 2 (.leaf _ k1963_1) (.leaf _ k1963_2)) (.split 3 (.leaf _ k1963_3) (.split 2 (.leaf _ k1963_4) (.leaf _ k1963_5)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1964)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k1964_0) (.leaf _ k1964_1)) (.split 3 (.leaf _ k1964_2) (.leaf _ k1964_3))) (.split 2 (.split 3 (.leaf _ k1964_4) (.leaf _ k1964_5)) (.split 3 (.leaf _ k1964_6) (.leaf _ k1964_7)))) (.split 3 (.split 3 (.split 2 (.leaf _ k1964_8) (.leaf _ k1964_9)) (.split 2 (.leaf _ k1964_10) (.leaf _ k1964_11))) (.split 3 (.split 2 (.leaf _ k1964_12) (.leaf _ k1964_13)) (.split 2 (.leaf _ k1964_14) (.leaf _ k1964_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1965)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k1965_0) (.leaf _ k1965_1)) (.split 1 (.leaf _ k1965_2) (.leaf _ k1965_3))) (.split 2 (.leaf _ k1965_4) (.leaf _ k1965_5))) (.split 3 (.split 2 (.split 1 (.leaf _ k1965_6) (.leaf _ k1965_7)) (.split 3 (.leaf _ k1965_8) (.leaf _ k1965_9))) (.split 2 (.leaf _ k1965_10) (.split 1 (.leaf _ k1965_11) (.leaf _ k1965_12))))))

end C4.Cert.Dir020
