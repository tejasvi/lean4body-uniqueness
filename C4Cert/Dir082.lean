module

public import C4Check

public section

/-! Cells `3140 ≤ n < 3165` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir082

theorem k3140_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).1 1).1
      85420955539170584359189689253713204118083409180856134819392326777809445264437308074830129035296250627446306811782285216543987).isSome = true := by
  decide +kernel

theorem k3140_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).1 1).2
      1157347159041906093997584704170494152919419099419528371486166185030603912929393834126399530190464998560499).isSome = true := by
  decide +kernel

theorem k3140_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).2 1).1 3).1
      290004779657062444727297056804484085692894041564943196064945518702661797296474204231601610663175577392956).isSome = true := by
  decide +kernel

theorem k3140_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).2 1).1 3).2
      207767082948725042997339885783928509869256755184854165047106876).isSome = true := by
  decide +kernel

theorem k3140_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).2 1).2 3).1
      15714084004809793357284150432710637648365819085330070732323158451782773361648101085554).isSome = true := by
  decide +kernel

theorem k3140_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).2 1).2 3).2
      830748719505390308266771919350852545651704616560988551426700476).isSome = true := by
  decide +kernel

theorem k3140_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).2 2).1
      6292083776186906367556105611217963716335020847629472492543883656133338097650403630016564368978961203900493541913815155381150519362143901533365709).isSome = true := by
  decide +kernel

theorem k3140_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).2 2).2 1).1
      72256672358220019460965261810577277734371891622861359605862433356857551234364036343712140783174141179123).isSome = true := by
  decide +kernel

theorem k3140_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).2 2).2 1).2
      18059560465142536772204498696794467387037405885503994949251569084146938829031347970443980186089416254919).isSome = true := by
  decide +kernel

theorem k3140_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).1 3).1 1).1
      985386961613150909629560412507210533410234501696902770971255767117200698067212694764).isSome = true := by
  decide +kernel

theorem k3140_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).1 3).1 1).2
      3931570299035923829661737514217645071530491049801458810495790367493892772092714669884).isSome = true := by
  decide +kernel

theorem k3140_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).1 3).2 1).1
      981709873001900751919312923853838719642343354806654397895966759517208222524651205868).isSome = true := by
  decide +kernel

theorem k3140_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).1 3).2 1).2
      61338293372632187690205013441345828721714674018124852093701519119936826473877722940).isSome = true := by
  decide +kernel

theorem k3140_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).2 3).1 1).1
      1161858170898161546720227827149467057811850743063863524744483628363523228813257252575107579367934716639665).isSome = true := by
  decide +kernel

theorem k3140_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).2 3).1 1).2
      985901179809457109923945916000578268745494336851370390634077288634968479797857474364).isSome = true := by
  decide +kernel

theorem k3140_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).2 3).2 1).1
      245634256978448668325272304113148436166933908694830859266213111653302100686615969196).isSome = true := by
  decide +kernel

theorem k3140_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).2 3).2 1).2
      982199951714082284968716285234858379710837740289957381727207722622108502492804798268).isSome = true := by
  decide +kernel

theorem k3140_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).1 1).1
      85329964092612874461639999943341296878416018138698253398909177624364210307160637166731626367717598762229810006486139726034163).isSome = true := by
  decide +kernel

theorem k3140_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).1 1).2
      341204425514050176609769989737577480141631460325845913333068023459628254103000819075921444023633753011398171210678980686738675).isSome = true := by
  decide +kernel

theorem k3140_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).2 1).1
      25196425235274673950653931887977827767547181570424809973675919075453299674768743489154370968424092258025146616981272170474326426469912444264642227).isSome = true := by
  decide +kernel

theorem k3140_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).2 1).2
      74018895571266371339052018848076538583291858927485870852403053569005812133255041482231415352099482450949363).isSome = true := by
  decide +kernel

theorem k3141_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3141) 2).1
      69447077679460631539181356701400611912881710149286697988276179378148811764352383623933359424107892607929806487891600732354781478405459069012933913581375952011274804092101596770174502238).isSome = true := by
  decide +kernel

theorem k3141_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).1 2).1
      1855039188696358334066990854739979452913718667869520797278286481264484006938687482955346427572608166810412502083744525754625336575936907340310249256165009616850666951).isSome = true := by
  decide +kernel

theorem k3141_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).1 2).2 3).1
      85259030867543743232019110991153363762845504386826791875032833678440029509662497438988154791566375780162035861803257596632497).isSome = true := by
  decide +kernel

theorem k3141_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).1 2).2 3).2
      61128275640479219775143708165533281084676199786083958923584199253463824713910613425).isSome = true := by
  decide +kernel

theorem k3141_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).2 2).1
      72080537198631510080091926816728195442498218293047550638430719026868566468029728393645681510169457124805).isSome = true := by
  decide +kernel

theorem k3141_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).2 2).2
      463899185818989223813762397336860156255578584892481235925065987051775100720949647608857120272537788846717813357296605539636080659704524559569675838233308104976295365).isSome = true := by
  decide +kernel

theorem k3142_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3142) 2).1
      261).isSome = true := by
  decide +kernel

theorem k3142_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3142) 2).2 2).1
      107575871164576695450499858183133010500360860746147815488344085959).isSome = true := by
  decide +kernel

theorem k3142_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3142) 2).2 2).2
      84969931767912354092359421069491888342678105646176029763932638806804165135218028739200330370685352321768261982495602421856535).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3143 3165 [
    4363585030, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3140 3165 :=
  (Cover.one (box := dirCellBox) (n := 3140)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3140_0) (.leaf _ k3140_1)) (.split 1 (.split 3 (.leaf _ k3140_2) (.leaf _ k3140_3)) (.split 3 (.leaf _ k3140_4) (.leaf _ k3140_5)))) (.split 2 (.leaf _ k3140_6) (.split 1 (.leaf _ k3140_7) (.leaf _ k3140_8)))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3140_9) (.leaf _ k3140_10)) (.split 1 (.leaf _ k3140_11) (.leaf _ k3140_12))) (.split 3 (.split 1 (.leaf _ k3140_13) (.leaf _ k3140_14)) (.split 1 (.leaf _ k3140_15) (.leaf _ k3140_16)))) (.split 2 (.split 1 (.leaf _ k3140_17) (.leaf _ k3140_18)) (.split 1 (.leaf _ k3140_19) (.leaf _ k3140_20)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3141)
      (.split 2 (.leaf _ k3141_0) (.split 3 (.split 2 (.leaf _ k3141_1) (.split 3 (.leaf _ k3141_2) (.leaf _ k3141_3))) (.split 2 (.leaf _ k3141_4) (.leaf _ k3141_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3142)
      (.split 2 (.leaf _ k3142_0) (.split 2 (.leaf _ k3142_1) (.leaf _ k3142_2)))).trans <|
  (Cover.dir c3)

end C4.Cert.Dir082
