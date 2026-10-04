module

public import C4Check

public section

/-! Cells `2354 ≤ n < 2355` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir034

theorem k2354_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).1 2).1 3).1
      1053331060402020963390203775487773921611486626456804624933169010340256845230776953696326).isSome = true := by
  decide +kernel

theorem k2354_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).1 2).1 3).2
      5694951745931873395670950954072182298843274209418645274544810450450817514666632820077683749250010805487242284415100279863854150).isSome = true := by
  decide +kernel

theorem k2354_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).1 2).2
      32682214855995273265338969107549778889008326032398264973185397291208324039818358686833844750232304275803282764473688685784077679890717960429420489042644631615237519705522567).isSome = true := by
  decide +kernel

theorem k2354_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).2 2).1 3).1
      353845919157063963248182159122811362580208146784236005588673219362085309904972834140789880624097133408941177181460177188791393).isSome = true := by
  decide +kernel

theorem k2354_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).2 2).1 3).2
      1409697778002713283241874787454849183776314409613781631530904390708724256211623393946957844405087023667180095915612237703312481).isSome = true := by
  decide +kernel

theorem k2354_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).2 2).2 3).1
      355538750229842199688693704522929198075221824352005071348529011871308599126532461961032013844675886006333856702111684071973985).isSome = true := by
  decide +kernel

theorem k2354_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).2 2).2 3).2
      353621190288348203358467153055749274376468712332749485219160734592475391134888193156109076240738692232761850088600946821284961).isSome = true := by
  decide +kernel

theorem k2354_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).1 2).1
      92036886472511022588274509217505260858458545079332833689762667338380507725739393444125592892834063924358214963764568521875474503).isSome = true := by
  decide +kernel

theorem k2354_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).1 2).2
      78155177666916446526445855070550246165310686717039624820678606939098511403884682248713465247551490041409607).isSome = true := by
  decide +kernel

theorem k2354_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).2 2).1 3).1
      302518272010448144990740349617389789526803461311269681919123546492048680884424821716525338351173039891553).isSome = true := by
  decide +kernel

theorem k2354_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).2 2).1 3).2
      355015021443325547447682001795432597986562632584730200722121843840007657565416163299203508893424458060653472140210924627534945).isSome = true := by
  decide +kernel

theorem k2354_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).2 2).2
      26923632925580370704655881250249768324624241832773148056208824976918814613687597097600073933571477452326949028231677753862533113522591643416797840455).isSome = true := by
  decide +kernel

theorem k2354_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).1 3).1 1).1
      39095037913080101106705).isSome = true := by
  decide +kernel

theorem k2354_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).1 3).1 1).2
      6620963988811951733407228184003086523128638847286696510287187141538790511299427373206808996194028884051254115981452673804333445577882156834081736134).isSome = true := by
  decide +kernel

theorem k2354_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).1 3).2 1).1
      179846083246469622342599024321472970276882).isSome = true := by
  decide +kernel

theorem k2354_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).1 3).2 1).2
      21831494135193898811350036935665230184132228575196346607336920217081167391156883240030608552606119911176769990590926023384498).isSome = true := by
  decide +kernel

theorem k2354_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).2 3).1
      1662212707352069810326135453668185056860671767515583093448424224871994261932139869235357527346616036107393622868523186054741417807827794524578119941).isSome = true := by
  decide +kernel

theorem k2354_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).2 3).2
      6621543145088916615041814458377568911580518602933809536529476947128331922623346235585564212287771525023623862902071007667032889681661316294661099589).isSome = true := by
  decide +kernel

theorem k2354_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).1 3).1 1).1
      2868073170197083487306593582822449311976737).isSome = true := by
  decide +kernel

theorem k2354_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).1 3).1 1).2
      21763317070414818095225481682369498697353609487639957595878345624518708869965153292232658643141320772382850371443087931563442).isSome = true := by
  decide +kernel

theorem k2354_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).1 3).2 1).1
      15578819320115108194049783135049421750501927761297025429912452078633031278176819570).isSome = true := by
  decide +kernel

theorem k2354_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).1 3).2 1).2
      4706547547356142973194039611428103253603089503478345315359871385800170999272757619946929785612606414515590).isSome = true := by
  decide +kernel

theorem k2354_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).2 3).1 1).1
      2877424825262863261884770082193671021084961).isSome = true := by
  decide +kernel

theorem k2354_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).2 3).1 1).2
      21831953464141624824317817353755259241311105822849915588535710075633689800824052671317041928049075857817077014381257858178482).isSome = true := by
  decide +kernel

theorem k2354_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).2 3).2 1).1
      15624006250103359542188755926350071923217577709474332931551810764589974395149905266).isSome = true := by
  decide +kernel

theorem k2354_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).2 3).2 1).2
      21765716770860669742222537790482799108617903164067284856930956616172553821775736253917740236543761413131334129714153842236850).isSome = true := by
  decide +kernel

theorem k2354_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).1 2).1 3).1
      417064904070694428705773698675130949505182569613767996319154862660016419319850813858190059388783899237935389109352276553409982934229975666706461957).isSome = true := by
  decide +kernel

theorem k2354_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).1 2).1 3).2
      415251110014755669163843100520561464867472102707731266867139162684941528575278964778116368210595866164442975316201569323863916454364039128934117637).isSome = true := by
  decide +kernel

theorem k2354_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).1 2).2 3).1
      4798606623546597817869616856581259384406937669351022306224564893002705817799619857571129324370486439433477).isSome = true := by
  decide +kernel

theorem k2354_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).1 2).2 3).2
      305727027883839558464947321847713581527222146130374881332483588886883567152776106694597450479363282986624261).isSome = true := by
  decide +kernel

theorem k2354_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).1 3).1 1).1
      721218599150154860702059572914868781884865).isSome = true := by
  decide +kernel

theorem k2354_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).1 3).1 1).2
      21899595518672678058425229726641353941339757113901746159765209503260322688264214846514721732989764287388198361419264378887602).isSome = true := by
  decide +kernel

theorem k2354_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).1 3).2 1).1
      11513048618117689498694881983863719570398221).isSome = true := by
  decide +kernel

theorem k2354_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).1 3).2 1).2
      21826905880033169702659604066849050934032533195070468312967409093221734080608415388681770225411279228449843381776767988686258).isSome = true := by
  decide +kernel

theorem k2354_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).2 3).1
      359511868515528022833192995987296246908314752304121799737162230550128044121514983039084280843881834462002670309835642663028594437).isSome = true := by
  decide +kernel

theorem k2354_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).2 3).2
      22928932676591584451413428724804377623236531818670172338242385974130243217222941777710925495535632216838735409778823930133994631221).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2354 2355 :=
  (Cover.one (box := dirCellBox) (n := 2354)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2354_0) (.leaf _ k2354_1)) (.leaf _ k2354_2)) (.split 2 (.split 3 (.leaf _ k2354_3) (.leaf _ k2354_4)) (.split 3 (.leaf _ k2354_5) (.leaf _ k2354_6)))) (.split 3 (.split 2 (.leaf _ k2354_7) (.leaf _ k2354_8)) (.split 2 (.split 3 (.leaf _ k2354_9) (.leaf _ k2354_10)) (.leaf _ k2354_11)))) (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2354_12) (.leaf _ k2354_13)) (.split 1 (.leaf _ k2354_14) (.leaf _ k2354_15))) (.split 3 (.leaf _ k2354_16) (.leaf _ k2354_17))) (.split 2 (.split 3 (.split 1 (.leaf _ k2354_18) (.leaf _ k2354_19)) (.split 1 (.leaf _ k2354_20) (.leaf _ k2354_21))) (.split 3 (.split 1 (.leaf _ k2354_22) (.leaf _ k2354_23)) (.split 1 (.leaf _ k2354_24) (.leaf _ k2354_25))))) (.split 3 (.split 2 (.split 3 (.leaf _ k2354_26) (.leaf _ k2354_27)) (.split 3 (.leaf _ k2354_28) (.leaf _ k2354_29))) (.split 2 (.split 3 (.split 1 (.leaf _ k2354_30) (.leaf _ k2354_31)) (.split 1 (.leaf _ k2354_32) (.leaf _ k2354_33))) (.split 3 (.leaf _ k2354_34) (.leaf _ k2354_35)))))))

end C4.Cert.Dir034
