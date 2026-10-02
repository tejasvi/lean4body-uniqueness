module

public import C4Check

public section

/-! Cells `3138 ≤ n < 3139` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir084

theorem k3138_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).1 1).1
      781295204851095037437706613154598531235640158832883).isSome = true := by
  decide +kernel

theorem k3138_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).1 1).2
      4056103638034050070619024944132585273768519129989771674752547486669087413379713798855).isSome = true := by
  decide +kernel

theorem k3138_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).2 1).1
      221366334735009922898951073579956931191038673512716083352124770876).isSome = true := by
  decide +kernel

theorem k3138_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).1 2).2 1).2
      4689844164903606605491194077625648096327861740114122706921912548172099706407739453094953032176663615347).isSome = true := by
  decide +kernel

theorem k3138_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).1
      89729978145757134708272916596320629769167065191775394950144646748185990957387755717595758554458128195108236287491985758332901617).isSome = true := by
  decide +kernel

theorem k3138_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).1 3).2 2).2
      22486948547826579222959930090937593990808485317483359622207062251938914538532072029334200771346859981222065313499828328999672049).isSome = true := by
  decide +kernel

theorem k3138_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).1 2).1
      55500378051995230916206280756143954032280082494216838125902492220).isSome = true := by
  decide +kernel

theorem k3138_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).1 2).2
      55645009684915776408678316223910641183544339766647083479310135868).isSome = true := by
  decide +kernel

theorem k3138_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).1 1).2
      5713594999990153817724557625838769055227251775635800487264907304918243130737507438212468705841632787177305203016993026105507250).isSome = true := by
  decide +kernel

theorem k3138_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 1).1 2).1
      47561250165081511845317602462038209145804933692).isSome = true := by
  decide +kernel

theorem k3138_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 1).1 2).2
      11918906224002125952245976885697945940584165948).isSome = true := by
  decide +kernel

theorem k3138_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).1 2).2 3).2 1).2
      4781053235865487626937237461236131774664610806757760781574460076710217443703128756758554296810015141813682).isSome = true := by
  decide +kernel

theorem k3138_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).1 1).1
      19321279572426293029773863035165836793945849488255289626156535231641271015634121064380102710853924057114990835).isSome = true := by
  decide +kernel

theorem k3138_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).1 1).2
      87130554489575544769545362203563390731233488870616893198290224996069389141958202973457855790415833714550755257486713858389234).isSome = true := by
  decide +kernel

theorem k3138_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).2 1).1
      4072090121814057132428789717640446274447303933056266809065447371292060829211686130054385).isSome = true := by
  decide +kernel

theorem k3138_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).1 3).2 1).2
      293341915239982927765017268009985392420583689486524881991501107001780390978584383994623116349744610793276).isSome = true := by
  decide +kernel

theorem k3138_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 1).1
      4855308677094869437293198513396220169597937092076480622951777191309511589813351169754383831688918905996489532).isSome = true := by
  decide +kernel

theorem k3138_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).1 1).2
      21865788094959721382277170029757428886140046166087355949736426555434804107661872256205135879289480124172939046598475698625970).isSome = true := by
  decide +kernel

theorem k3138_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).2 1).1
      4089666121538818185010586155977231647923030114550040964300712727960964459942384139007218).isSome = true := by
  decide +kernel

theorem k3138_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).1 3).2 2).2 3).2 1).2
      294225758775117621731952481080934464917061877333444098948258005911128595943030367256057635889839733200700).isSome = true := by
  decide +kernel

theorem k3138_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).1 1).1
      26524532758477544014117219306644651477519004792201787442646391910874987399053368519644503864427264903782015389557796530683329147137311636499037618).isSome = true := by
  decide +kernel

theorem k3138_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).1 1).2
      65902123116686572022347443484831461801716683456050010573551285657696300366827892087986).isSome = true := by
  decide +kernel

theorem k3138_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).2 1).1
      77888434067915091308633062702047182131609602082053957953293759457919419801958569088610653674417190735541491).isSome = true := by
  decide +kernel

theorem k3138_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).1 2).2 1).2
      4134482879912017739442812852207841970826868377319060274154779231550498402298314659634).isSome = true := by
  decide +kernel

theorem k3138_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 1).1
      3703464542868334273167961418426005149975764014698528660375061990370429170).isSome = true := by
  decide +kernel

theorem k3138_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).1 1).2
      260305418444685684237740213767597638824682523624089188354604374557090798447224686211762).isSome = true := by
  decide +kernel

theorem k3138_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).2 1).1
      1046245766087732739327597511956190447824713460515081077115984239531400848906652918837938).isSome = true := by
  decide +kernel

theorem k3138_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).1 3).2 2).2 1).2
      16330070325032191468746376205103851932427186983719351940097459142145215262328790801586).isSome = true := by
  decide +kernel

theorem k3138_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).1 1).1
      16509802805443176479755197965855355486660271162470575623514697622197531241305516541987388).isSome = true := by
  decide +kernel

theorem k3138_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).1 1).2
      16108672629876421319413400612327485452051277289311550493368053993671894625027442070332).isSome = true := by
  decide +kernel

theorem k3138_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).2 1).1
      16010927114045620747145722950008827628984556472229390100789403595169902964938844796476).isSome = true := by
  decide +kernel

theorem k3138_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).1 3).2 1).2
      999647928896751795037021349902419775047468213704586684302557015353569753741274773052).isSome = true := by
  decide +kernel

theorem k3138_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).1 1).1
      194818060645795789578775285007731573158251107873010).isSome = true := by
  decide +kernel

theorem k3138_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).1 1).2
      54748292943373983411585624223484182608726925961439690359696650812).isSome = true := by
  decide +kernel

theorem k3138_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).2 1).1
      11793074770718051212174268731731657778901938748).isSome = true := by
  decide +kernel

theorem k3138_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3138) 2).2 3).2 2).2 3).2 1).2
      217331636380769193772727067547735171116407090938358873332213336636).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3138 3139 :=
  (Cover.one (box := dirCellBox) (n := 3138)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3138_0) (.leaf _ k3138_1)) (.split 1 (.leaf _ k3138_2) (.leaf _ k3138_3))) (.split 2 (.leaf _ k3138_4) (.leaf _ k3138_5))) (.split 3 (.split 1 (.split 2 (.leaf _ k3138_6) (.leaf _ k3138_7)) (.leaf _ k3138_8)) (.split 1 (.split 2 (.leaf _ k3138_9) (.leaf _ k3138_10)) (.leaf _ k3138_11)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3138_12) (.leaf _ k3138_13)) (.split 1 (.leaf _ k3138_14) (.leaf _ k3138_15))) (.split 3 (.split 1 (.leaf _ k3138_16) (.leaf _ k3138_17)) (.split 1 (.leaf _ k3138_18) (.leaf _ k3138_19))))) (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k3138_20) (.leaf _ k3138_21)) (.split 1 (.leaf _ k3138_22) (.leaf _ k3138_23))) (.split 2 (.split 1 (.leaf _ k3138_24) (.leaf _ k3138_25)) (.split 1 (.leaf _ k3138_26) (.leaf _ k3138_27)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3138_28) (.leaf _ k3138_29)) (.split 1 (.leaf _ k3138_30) (.leaf _ k3138_31))) (.split 3 (.split 1 (.leaf _ k3138_32) (.leaf _ k3138_33)) (.split 1 (.leaf _ k3138_34) (.leaf _ k3138_35)))))))

end C4.Cert.Dir084
