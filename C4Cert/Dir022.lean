module

public import C4Check

public section

/-! Cells `1993 ≤ n < 1997` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir022

theorem k1993_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).1 3).1 1).1
      87546653918692865634224199659992549098946371680789925068758155795265438369240272823581195320645212344824038685434629428541555910).isSome = true := by
  decide +kernel

theorem k1993_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).1 3).1 1).2
      5470316778011746381075622831125904720268950071675744353746470638882317314682308657276594859956441204152729550361896457129548594).isSome = true := by
  decide +kernel

theorem k1993_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).1 3).2 1).1
      251149110933202322736208884594574723808343773171388518572901474089007205984421533474018).isSome = true := by
  decide +kernel

theorem k1993_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).1 3).2 1).2
      5463907722071054496442546153125556360180519303070904363211942121071497616539971055201034241377873045680145421246811334585473842).isSome = true := by
  decide +kernel

theorem k1993_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).1 1).1
      87663747814932054832512806143803675135676636040663287108532099088339431254979184059928429251298602736521313739413537111861171398).isSome = true := by
  decide +kernel

theorem k1993_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).1 1).2
      350516814100439364149893445613773279136677365506400503566811070338936591563736623033578051582629598958848031357026668095456366386).isSome = true := by
  decide +kernel

theorem k1993_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).2 1).1 2).1
      61305237417007310405540792623942131054920887333343411064225295880902575671659059148).isSome = true := by
  decide +kernel

theorem k1993_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).2 1).1 2).2
      61338707606708332682782705379021915172173567276948737191913122741631593875011655628).isSome = true := by
  decide +kernel

theorem k1993_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).2 1).2
      5469764799414314098582049970788407366159356958756193552611117144901401824233812750369859756821953988635860351378364005901261618).isSome = true := by
  decide +kernel

theorem k1993_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).1 2).1 1).1
      15666062608294057069931651827564719653062806772391253587258561439704702235013413690595).isSome = true := by
  decide +kernel

theorem k1993_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).1 2).1 1).2
      250361912772284194217122085094090985383180092479403916797347334654980159365482171934343).isSome = true := by
  decide +kernel

theorem k1993_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).1 2).2 3).1
      256537544889965213162561878011534947734838405570485891882667994278174108433758617029598433).isSome = true := by
  decide +kernel

theorem k1993_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).1 2).2 3).2
      16021681938703176327515830549460192604288713184838251607466948782417521991293848840140421).isSome = true := by
  decide +kernel

theorem k1993_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).2 3).1 1).1
      5464104618635697276199546902598617906388422256318144602583334547339917737803866978671537510383967494414069221029897632452303666).isSome = true := by
  decide +kernel

theorem k1993_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).2 3).1 1).2
      5463514425757202023176380527308083663151002443689648938931025763603951379676005061574944070870397042399399473088587786043644722).isSome = true := by
  decide +kernel

theorem k1993_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).2 3).2 1).1
      295848040815842846440447348361992118179580158879966570140382719161512880075419630066290912995564973459687049).isSome = true := by
  decide +kernel

theorem k1993_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).2 3).2 1).2
      4104264181217166404874091741858388097905185366613544586547717048860984604292108868627319601).isSome = true := by
  decide +kernel

theorem k1994_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).1 2).1
      22295646346826499535002292372792376510370574582907679909527185228388964243528410217846171686076679608486564672119520414714386271117).isSome = true := by
  decide +kernel

theorem k1994_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).1 2).2 1).1
      15634237304557992759214455994602387059996459877520743945193284366988997466275559923251).isSome = true := by
  decide +kernel

theorem k1994_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).1 2).2 1).2
      3907698064578806975489588724001085564326988706452967544280861191402582172005031876403).isSome = true := by
  decide +kernel

theorem k1994_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).2 2).1
      73870992241894155087472781597782114661433150552094037040691212937905555275999953402329898640384198368515981).isSome = true := by
  decide +kernel

theorem k1994_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1994) 2).1 3).2 2).2
      348226680270330486241564203724084572352473147375360791873459028222026482001800244977680473047893738945451199446797189055614766897).isSome = true := by
  decide +kernel

theorem k1994_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).1 1).1 3).1
      1001300837375882553801436077579342488636947974772335894205251836431800339089445067518689).isSome = true := by
  decide +kernel

theorem k1994_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).1 1).1 3).2
      1000614838722291068988687745989335169457565915533772623867980805608095246287393003500337).isSome = true := by
  decide +kernel

theorem k1994_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).1 1).2 3).1
      1001223774035526244564807586613163211799525666242044307203497328743048493307345535595313).isSome = true := by
  decide +kernel

theorem k1994_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).1 1).2 3).2
      1000483563841148960551465047828192234068264252147948126056413834510017901035912120857393).isSome = true := by
  decide +kernel

theorem k1994_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).2 1).1 3).1
      3389600167433202140243763158583534634051364418903785652946031168306).isSome = true := by
  decide +kernel

theorem k1994_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).2 1).1 3).2
      211616723155568108999032101330742215704905748028389085968382416690).isSome = true := by
  decide +kernel

theorem k1994_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).2 1).2 2).1
      3307422790870851219682866434780224396512423862626860066619642828).isSome = true := by
  decide +kernel

theorem k1994_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1994) 2).2 3).2 1).2 2).2
      15621965680680439492645209846429492503321708370571989077532773311295495480272392642099).isSome = true := by
  decide +kernel

theorem k1995_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).1 3).1 2).1
      15596824308777916907985361881317311821134482750390754695148990144566525016819298834225).isSome = true := by
  decide +kernel

theorem k1995_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).1 3).1 2).2
      1151188852641890726309958825257004070534890706338471103521949669210129586606630240391566637038764633710385).isSome = true := by
  decide +kernel

theorem k1995_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).1 3).2 1).1
      243600298257091550335258040874630481520646129429842306609701759972267297149940009330).isSome = true := by
  decide +kernel

theorem k1995_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).1 3).2 1).2
      3896965527409537120134942849809124192319643937659742870061731903589143428541575452467).isSome = true := by
  decide +kernel

theorem k1995_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).2 3).1 1).1
      1022295255263738598172030144923835566739240192572101111007871712333379545913047638239202099).isSome = true := by
  decide +kernel

theorem k1995_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).2 3).1 1).2
      5436700923014475925587046708077339803519723659605762935520666423380965765111139563286309205865179046547046686422679212939139891).isSome = true := by
  decide +kernel

theorem k1995_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).2 3).2 1).1
      4602878473912096682513478475490459173988298477975890178483349436452216544696790760083810937289895531124530).isSome = true := by
  decide +kernel

theorem k1995_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1995) 2).2 3).2 1).2
      3898783445128838371288767337897508635661911702270411947356975481986039239273762608946).isSome = true := by
  decide +kernel

theorem k1996_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).1 3).1
      1357531580161060775472072110999013126559158179642465640147435647470334500273576943365878627632068340812102235361750490262640525).isSome = true := by
  decide +kernel

theorem k1996_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).1 3).2
      71824518293398958007955124570129179557639881009213540027040315857033632025551072863679708773657321019209).isSome = true := by
  decide +kernel

theorem k1996_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).2 3).1
      88972139913908354082920555790357358710957960795385231689736775326436524913407231294853777249014999278013989518711683317274801364173).isSome = true := by
  decide +kernel

theorem k1996_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1996) 2).2 3).2
      347331825461715170395460357304798675526504788361541169171741975384990552409488091576485884806823511123792260253793108297862451913).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1993 1997 :=
  (Cover.one (box := dirCellBox) (n := 1993)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k1993_0) (.leaf _ k1993_1)) (.split 1 (.leaf _ k1993_2) (.leaf _ k1993_3))) (.split 3 (.split 1 (.leaf _ k1993_4) (.leaf _ k1993_5)) (.split 1 (.split 2 (.leaf _ k1993_6) (.leaf _ k1993_7)) (.leaf _ k1993_8)))) (.split 2 (.split 2 (.split 1 (.leaf _ k1993_9) (.leaf _ k1993_10)) (.split 3 (.leaf _ k1993_11) (.leaf _ k1993_12))) (.split 3 (.split 1 (.leaf _ k1993_13) (.leaf _ k1993_14)) (.split 1 (.leaf _ k1993_15) (.leaf _ k1993_16)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1994)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1994_0) (.split 1 (.leaf _ k1994_1) (.leaf _ k1994_2))) (.split 2 (.leaf _ k1994_3) (.leaf _ k1994_4))) (.split 3 (.split 1 (.split 3 (.leaf _ k1994_5) (.leaf _ k1994_6)) (.split 3 (.leaf _ k1994_7) (.leaf _ k1994_8))) (.split 1 (.split 3 (.leaf _ k1994_9) (.leaf _ k1994_10)) (.split 2 (.leaf _ k1994_11) (.leaf _ k1994_12)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1995)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1995_0) (.leaf _ k1995_1)) (.split 1 (.leaf _ k1995_2) (.leaf _ k1995_3))) (.split 3 (.split 1 (.leaf _ k1995_4) (.leaf _ k1995_5)) (.split 1 (.leaf _ k1995_6) (.leaf _ k1995_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1996)
      (.split 2 (.split 3 (.leaf _ k1996_0) (.leaf _ k1996_1)) (.split 3 (.leaf _ k1996_2) (.leaf _ k1996_3))))

end C4.Cert.Dir022
