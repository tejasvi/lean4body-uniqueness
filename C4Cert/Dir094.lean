module

public import C4Check

public section

/-! Cells `3233 ≤ n < 3254` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir094

theorem c0 : allCells dirCell 3233 3250 [
    4589261862026151803882256296225157096157714374131442328524995871709438484379730457085870786657455068901446,
    44614249749930013664039924653553866481340678, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c1 : allCells dirCell 3250 3251 [
    529081712314975202423212692125761457348098190627007579413560345839335717914771425411714663266986151711762109883032930933045516231059368183283850965880789619801649646372524134799] = true := by
  decide +kernel

theorem k3251_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).1 2).1 3).1
      352379930797463026505374508662249327764801332967958884819277875966208091214986747509396807497813314888523321222938886555399410).isSome = true := by
  decide +kernel

theorem k3251_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).1 2).1 3).2
      5609460331789776245584289541859046386276128101110998752576732451661157058191697831863797130739663199769339192781818919602189553).isSome = true := by
  decide +kernel

theorem k3251_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).1 2).2 3).1
      15779984498602667086791820668169243546232544511325403815431177430361167668274072945).isSome = true := by
  decide +kernel

theorem k3251_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).1 2).2 3).2
      87652821502611429737269949497147557569219425076258783917197390520393182502138746762353272382324787177468964924202610692769225).isSome = true := by
  decide +kernel

theorem k3251_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).1 3).1 1).1
      4009699858802844237472389260810970646546694678523275541768203386225440349097043678012).isSome = true := by
  decide +kernel

theorem k3251_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).1 3).1 1).2
      250486128028188931007799950104327064638559413478614464884797966039559859145975365036).isSome = true := by
  decide +kernel

theorem k3251_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).1 3).2 1).1
      997840145716935440243110364872473038103271967262373503143744916199804163374310618684).isSome = true := by
  decide +kernel

theorem k3251_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).1 3).2 1).2
      3379201490618666014974544781294814389949172797537781060168212268).isSome = true := by
  decide +kernel

theorem k3251_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).2 3).1
      87220965585301062590651191988781281900374974177566456797759641005562668974164485377360336561869112243261430891690616323929329).isSome = true := by
  decide +kernel

theorem k3251_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3251) 3).2 2).2 3).2
      22251644013617447003702977736187279924134293869152718004010500472906828692853422541461904920866485767882232108178370553249363633).isSome = true := by
  decide +kernel

theorem k3252_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).1 3).1 2).1
      15904817921273888944996374301886381244150030540675272690746956992691198070888175131825).isSome = true := by
  decide +kernel

theorem k3252_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).1 3).1 2).2
      53915989368068539509658878612948577356142922274121972187763438140).isSome = true := by
  decide +kernel

theorem k3252_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).1 3).2 1).1
      1016641488871605523659534159934433619398952268094551994208628038208102097580540474946108).isSome = true := by
  decide +kernel

theorem k3252_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).1 3).2 1).2
      15879395232539605223979918366250174277848280823837213417431217516368664313120702708796).isSome = true := by
  decide +kernel

theorem k3252_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).2 2).1
      22150700395978522951587589826810176106257590681353666359210051344732398583041401622315966966889815235646668187022467540182465713).isSome = true := by
  decide +kernel

theorem k3252_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3252) 3).1 2).2 2).2
      22175964775746397661537383156537093487648103436848117302451465707723692047831062830474174014384161572362503613458027363272588465).isSome = true := by
  decide +kernel

theorem k3252_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).2 2).1 2).1 1).1
      15825865222722996777928871418257895999762268528765012567264393559215950432813524565052).isSome = true := by
  decide +kernel

theorem k3252_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).2 2).1 2).1 1).2
      3955168565840645911969581194155562711756055467833709650028497261761873014095447946188).isSome = true := by
  decide +kernel

theorem k3252_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).2 2).1 2).2 1).1
      15831234704540228233470825460360255814063752991980483812312098534811743546411858115644).isSome = true := by
  decide +kernel

theorem k3252_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3252) 3).2 2).1 2).2 1).2
      53621345817005008580959240793260277947027501951164291013170262988).isSome = true := by
  decide +kernel

theorem k3252_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3252) 3).2 2).2 1).1
      5651975538931737720078668055359439634152618737899537740018318189525789428031579623033959582628142485724033986450062266102055366898).isSome = true := by
  decide +kernel

theorem k3252_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3252) 3).2 2).2 1).2
      1196415022918786921863535696967945622069606527596790961959303651883935604018816329018519292573869156528126770).isSome = true := by
  decide +kernel

theorem k3253_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).1 2).1 1).1
      3418417866030326330364352155109143580902245584718283222269229317180).isSome = true := by
  decide +kernel

theorem k3253_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).1 2).1 1).2
      3417427475903558842740799971101228225446816880154535538817145942988).isSome = true := by
  decide +kernel

theorem k3253_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).1 2).2 1).1
      854906369600515897719028094990129267175737843933388730321745001532).isSome = true := by
  decide +kernel

theorem k3253_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).1 2).2 1).2
      213667660615129662410089727426159360144848934782601579798174707404).isSome = true := by
  decide +kernel

theorem k3253_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).2 1).1 2).1
      855172430834833324514697481201745192977309941302188521940489911356).isSome = true := by
  decide +kernel

theorem k3253_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).2 1).1 2).2
      46368904941432062932056960977714527312731106364).isSome = true := by
  decide +kernel

theorem k3253_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3253) 3).1 2).2 1).2
      4767946646054299285172475308424436673401657042935218963291822963191229366729126670361962112438532296332114738).isSome = true := by
  decide +kernel

theorem k3253_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).1 2).1 1).1
      3411820352774095529273935699590906697590694523360888919471670737980).isSome = true := by
  decide +kernel

theorem k3253_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).1 2).1 1).2
      53247840903588546093438057783599758917069053512834796935705097164).isSome = true := by
  decide +kernel

theorem k3253_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).1 2).2 1).1
      3409653528641356197450970890319575261701728720974592134750016420924).isSome = true := by
  decide +kernel

theorem k3253_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).1 2).2 1).2
      2887278065683816492726540764879924613796671180).isSome = true := by
  decide +kernel

theorem k3253_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).2 1).1 2).1
      852668080663573065080775566639563229275206056218755392959657327676).isSome = true := by
  decide +kernel

theorem k3253_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).2 1).1 2).2
      11569023231457221639411529682569565183140883516).isSome = true := by
  decide +kernel

theorem k3253_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3253) 3).2 2).2 1).2
      19015928995154054778506560836236175862753307078895144731651258918937659968276192115180155544067088693038312242).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3233 3254 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 3251)
      (.split 3 (.split 2 (.split 3 (.leaf _ k3251_0) (.leaf _ k3251_1)) (.split 3 (.leaf _ k3251_2) (.leaf _ k3251_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k3251_4) (.leaf _ k3251_5)) (.split 1 (.leaf _ k3251_6) (.leaf _ k3251_7))) (.split 3 (.leaf _ k3251_8) (.leaf _ k3251_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3252)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3252_0) (.leaf _ k3252_1)) (.split 1 (.leaf _ k3252_2) (.leaf _ k3252_3))) (.split 2 (.leaf _ k3252_4) (.leaf _ k3252_5))) (.split 2 (.split 2 (.split 1 (.leaf _ k3252_6) (.leaf _ k3252_7)) (.split 1 (.leaf _ k3252_8) (.leaf _ k3252_9))) (.split 1 (.leaf _ k3252_10) (.leaf _ k3252_11))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3253)
      (.split 3 (.split 2 (.split 2 (.split 1 (.leaf _ k3253_0) (.leaf _ k3253_1)) (.split 1 (.leaf _ k3253_2) (.leaf _ k3253_3))) (.split 1 (.split 2 (.leaf _ k3253_4) (.leaf _ k3253_5)) (.leaf _ k3253_6))) (.split 2 (.split 2 (.split 1 (.leaf _ k3253_7) (.leaf _ k3253_8)) (.split 1 (.leaf _ k3253_9) (.leaf _ k3253_10))) (.split 1 (.split 2 (.leaf _ k3253_11) (.leaf _ k3253_12)) (.leaf _ k3253_13)))))

end C4.Cert.Dir094
