module

public import C4Check

public section

/-! Cells `3139 ≤ n < 3140` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir081

theorem k3139_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).1 1).1 3).1
      63422988287340704072760641192280490472490046527385578812878087438637846057604583300529).isSome = true := by
  decide +kernel

theorem k3139_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).1 1).1 3).2
      989482477599300873018256924902749660553444094590410697208777552251872687085953873132).isSome = true := by
  decide +kernel

theorem k3139_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).1 1).2 2).1
      988929400302630308896750188993842560654202213760188388681373351505859846492985910513).isSome = true := by
  decide +kernel

theorem k3139_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).1 1).2 2).2
      15837235716203764864144881797824517152987981597914319426681632411850604117375148844273).isSome = true := by
  decide +kernel

theorem k3139_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).2 1).1 3).1
      3951883634673476878053564613737075870466115016693616056593911799488810027884379362108).isSome = true := by
  decide +kernel

theorem k3139_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).2 1).1 3).2
      247156452658190290755207021014639024468408956429886988315697898169619264864880524716).isSome = true := by
  decide +kernel

theorem k3139_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).2 1).2
      406070202569301638028961339263522004655420370119941452644840342387162695913595026522087762679738303224281503600891224821083349520620673404905813234).isSome = true := by
  decide +kernel

theorem k3139_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).1 2).1 1).1
      63426305904490836695888302645595333078993118986288149189097315088530987775276644723123).isSome = true := by
  decide +kernel

theorem k3139_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).1 2).1 1).2
      3963514877681647276624773265560568287031406306683796377290838757305549812511135340977).isSome = true := by
  decide +kernel

theorem k3139_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).1 2).2 1).1
      4690153977167667279082790324172815663359063939606589807775153044175912869055756918871924060575966483668204).isSome = true := by
  decide +kernel

theorem k3139_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).1 2).2 1).2
      3968136874525186772913190451629861626595881214495936175805498323815591783026062399921).isSome = true := by
  decide +kernel

theorem k3139_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).2 1).1 2).1
      53582033235420775155007611228593748445498108286993135415905875180).isSome = true := by
  decide +kernel

theorem k3139_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).2 1).1 2).2
      53629693135734749593777183389079503183119136915473011307121603820).isSome = true := by
  decide +kernel

theorem k3139_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).2 1).2 2).1
      246920875236405672249500973965717012549505705318717948496634708737092779422774532529).isSome = true := by
  decide +kernel

theorem k3139_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).2 1).2 2).2
      214373701463952855530769034968426275152168700992979722049374638828).isSome = true := by
  decide +kernel

theorem k3139_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).1 3).1 1).1
      343151886690641610553661408417704368840877502584950782169494746591122576900350872253773460633463686727484467151628867222992113).isSome = true := by
  decide +kernel

theorem k3139_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).1 3).1 1).2
      342881694210201244983695771585581261838171413303011536968774533449743534865071340379825637453673068006932962841508406909302003).isSome = true := by
  decide +kernel

theorem k3139_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).1 3).2 1).1
      5353968532440394504575326904374289571557399073953322196801815405612103610625328449133669061366565041229953135540506195384124).isSome = true := by
  decide +kernel

theorem k3139_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).1 3).2 1).2
      4531859502832770937746494212690488307970867909422472415733479772574025448440229146987947560455225857521).isSome = true := by
  decide +kernel

theorem k3139_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).2 3).1 1).1
      101373400172244558899998682527502147021765105832206361573155319425884101820509218738983266114489918138284794688571929033109429732199251792860935859).isSome = true := by
  decide +kernel

theorem k3139_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).2 3).1 1).2
      16168708664210343495036613421245731862474850861275610081496001898367329892971107587355890).isSome = true := by
  decide +kernel

theorem k3139_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).2 3).2 1).1
      18585260916551655540085398211119797336780775192567420777784472312430489127222133575614760276941903093456305).isSome = true := by
  decide +kernel

theorem k3139_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).2 3).2 1).2
      290816706377040729966007119910058712776975869496481824897025359090855936903543283703762698458488918465724).isSome = true := by
  decide +kernel

theorem k3139_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).1 1).1 2).1
      1019990261390015419360622543335249406441441815324147190183995965095110785064631640337980).isSome = true := by
  decide +kernel

theorem k3139_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).1 1).1 2).2
      1018393785371277533184320363989587012652907596209183763986025034318786372810566127706803).isSome = true := by
  decide +kernel

theorem k3139_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).1 1).2 3).1
      221051019904467843299025604822250678020628081416954578692234328972722).isSome = true := by
  decide +kernel

theorem k3139_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).1 1).2 3).2
      15888538790922340655435350952399650315757015463159766406216398275738693120558709996972).isSome = true := by
  decide +kernel

theorem k3139_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).2 2).1 1).1
      215137572468939855971541886056913755650398523882952280584526227116).isSome = true := by
  decide +kernel

theorem k3139_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).2 2).1 1).2
      53742482012352108848561751195599827386274291887450925028209981100).isSome = true := by
  decide +kernel

theorem k3139_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).2 2).2 1).1
      214934459286239618867083843555028484674723710497831656182290835116).isSome = true := by
  decide +kernel

theorem k3139_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).2 2).2 1).2
      13424449364597673835491296395856730586454173451061655992026103212).isSome = true := by
  decide +kernel

theorem k3139_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).1 2).1 1).1
      65221219768775409462464721532185471092953698701756099475238828279682362194231755143612659).isSome = true := by
  decide +kernel

theorem k3139_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).1 2).1 1).2
      220785458729460122883792973716861857249196212454217257368331343198387).isSome = true := by
  decide +kernel

theorem k3139_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).1 2).2 1).1
      1021808723353662497633154076158947100724593804274881980196489074521508476458098094764604).isSome = true := by
  decide +kernel

theorem k3139_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).1 2).2 1).2
      55262877706091440308990923467186534972751840445336923540848378214579).isSome = true := by
  decide +kernel

theorem k3139_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).2 2).1 1).1
      860599734215627209359229981371895835580283452378290635129602677308).isSome = true := by
  decide +kernel

theorem k3139_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).2 2).1 1).2
      13438027440613570548213872724111198834442218325867852461683342764).isSome = true := by
  decide +kernel

theorem k3139_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).2 2).2 1).1
      63567823725181425879945970027837014282671530502613670663137852794879579642833674426940).isSome = true := by
  decide +kernel

theorem k3139_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).2 2).2 1).2
      13451843390585765242347982847611072674308672894591133215999229356).isSome = true := by
  decide +kernel

theorem k3139_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).1 1).1 3).1
      88129574637361838720788336470291351387306976735383364972150855083625951093468227772141750297608829984203015584456375902861239986).isSome = true := by
  decide +kernel

theorem k3139_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).1 1).1 3).2
      74457316274534223883393770679075669870071775318516017848459647231794914233374239308991015576317278666137010).isSome = true := by
  decide +kernel

theorem k3139_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).1 1).2 3).1
      19098836016292451799918700997860082426542887511516738236233540650933522995946081515261171165268129548754373554).isSome = true := by
  decide +kernel

theorem k3139_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).1 1).2 3).2
      1008579318750370680822620812795219324273752055606047590527276695611415614132078257927410).isSome = true := by
  decide +kernel

theorem k3139_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).2 3).1 1).1
      353117739293237526555258619839372990767667042296683977682328002695481223762137525908546794338967151203960749543817788160792196786).isSome = true := by
  decide +kernel

theorem k3139_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).2 3).1 1).2
      88253827538898790936244601703996543502137122122627847862473347593374667914475625123702515560943380798501507794472693581523864817).isSome = true := by
  decide +kernel

theorem k3139_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).2 3).2 1).1
      1193652542741540676833059392140217912423772405373540472467430894580309323893932035555717387641347866273035068).isSome = true := by
  decide +kernel

theorem k3139_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).2 3).2 1).2
      4662076867604167335530073787069938789053883726174632502928622750585263523848555366426869284921578066615730).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3139 3140 :=
  (Cover.one (box := dirCellBox) (n := 3139)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ k3139_0) (.leaf _ k3139_1)) (.split 2 (.leaf _ k3139_2) (.leaf _ k3139_3))) (.split 1 (.split 3 (.leaf _ k3139_4) (.leaf _ k3139_5)) (.leaf _ k3139_6))) (.split 3 (.split 2 (.split 1 (.leaf _ k3139_7) (.leaf _ k3139_8)) (.split 1 (.leaf _ k3139_9) (.leaf _ k3139_10))) (.split 1 (.split 2 (.leaf _ k3139_11) (.leaf _ k3139_12)) (.split 2 (.leaf _ k3139_13) (.leaf _ k3139_14))))) (.split 2 (.split 3 (.split 1 (.leaf _ k3139_15) (.leaf _ k3139_16)) (.split 1 (.leaf _ k3139_17) (.leaf _ k3139_18))) (.split 3 (.split 1 (.leaf _ k3139_19) (.leaf _ k3139_20)) (.split 1 (.leaf _ k3139_21) (.leaf _ k3139_22))))) (.split 3 (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3139_23) (.leaf _ k3139_24)) (.split 3 (.leaf _ k3139_25) (.leaf _ k3139_26))) (.split 2 (.split 1 (.leaf _ k3139_27) (.leaf _ k3139_28)) (.split 1 (.leaf _ k3139_29) (.leaf _ k3139_30)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3139_31) (.leaf _ k3139_32)) (.split 1 (.leaf _ k3139_33) (.leaf _ k3139_34))) (.split 2 (.split 1 (.leaf _ k3139_35) (.leaf _ k3139_36)) (.split 1 (.leaf _ k3139_37) (.leaf _ k3139_38))))) (.split 2 (.split 1 (.split 3 (.leaf _ k3139_39) (.leaf _ k3139_40)) (.split 3 (.leaf _ k3139_41) (.leaf _ k3139_42))) (.split 3 (.split 1 (.leaf _ k3139_43) (.leaf _ k3139_44)) (.split 1 (.leaf _ k3139_45) (.leaf _ k3139_46)))))))

end C4.Cert.Dir081
