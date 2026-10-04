module

public import C4Check

public section

/-! Cells `3167 ≤ n < 3168` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir085

theorem k3167_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).1 2).1 1).1
      1023079040385744297590634264961607364794859211348622881259500117933513925988735640334908).isSome = true := by
  decide +kernel

theorem k3167_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).1 2).1 1).2
      255562379475229706526723137616683646984960177306571388513890360549950182393179327036588).isSome = true := by
  decide +kernel

theorem k3167_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).1 2).2 1).1
      869133450889287182081853727776420541104798642232448923323900738620).isSome = true := by
  decide +kernel

theorem k3167_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).1 2).2 1).2
      3997219774740933866702017483725481887946240975272507374492646924021171417569912385324).isSome = true := by
  decide +kernel

theorem k3167_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).2 2).1 1).1
      3455608959374148339250735386537366633318314255327685230681456020028).isSome = true := by
  decide +kernel

theorem k3167_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).2 2).1 1).2
      186602517396393368662063166215329571925840665779).isSome = true := by
  decide +kernel

theorem k3167_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).2 2).2 1).1
      3452914144677878875040891735126214898621806052574197746580275589692).isSome = true := by
  decide +kernel

theorem k3167_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).1 3).2 2).2 1).2
      2922247939439964675323830160895256474843200684).isSome = true := by
  decide +kernel

theorem k3167_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).1 2).1 1).1
      868461379261602409660402925982012065776422310212113554032195124284).isSome = true := by
  decide +kernel

theorem k3167_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).1 2).1 1).2
      13878446516753797126815936611583504173577459564859585026072894201393).isSome = true := by
  decide +kernel

theorem k3167_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).1 2).2 1).1
      869348881806790417658464343154804831128326487385530720965988564028).isSome = true := by
  decide +kernel

theorem k3167_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).1 2).2 1).2
      54289357607190930959176879349042022681745389856128819412007762732).isSome = true := by
  decide +kernel

theorem k3167_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).2 2).1 1).1
      3459123733048124010596928570921769025575221426016186338647697977916).isSome = true := by
  decide +kernel

theorem k3167_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).2 2).1 1).2
      731267999658156769518187124178773020351491884).isSome = true := by
  decide +kernel

theorem k3167_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).2 2).2 1).1
      864784996116671282814074242656970192362478633788636763815872937020).isSome = true := by
  decide +kernel

theorem k3167_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).1 2).2 3).2 2).2 1).2
      2927859610393414123499312382985389559694061356).isSome = true := by
  decide +kernel

theorem k3167_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).1 1).1 3).1
      46623390553787450811793454560379364045806864956).isSome = true := by
  decide +kernel

theorem k3167_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).1 1).1 3).2
      858602895567464161256906268106974287018084741344756694415944174140).isSome = true := by
  decide +kernel

theorem k3167_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).1 1).2
      5519824973896674833119486602285193000207872500008322205513820298601335163995990040292773454547746845616833433926548323159107249).isSome = true := by
  decide +kernel

theorem k3167_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).2 1).1
      1193933817171719690599049450698872091407958907636997297293216222365922911816710772431152066324135056485354161).isSome = true := by
  decide +kernel

theorem k3167_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).1 3).2 1).2
      344388231496406045307289277973540411536951473142636321533972817598830427916601614202846378428289051807923908052076075656665004).isSome = true := by
  decide +kernel

theorem k3167_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).1 1).1 2).1
      11660794860233516135428090185483620451152814652).isSome = true := by
  decide +kernel

theorem k3167_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).1 1).1 2).2
      46725128027049128813604968292031801400888848956).isSome = true := by
  decide +kernel

theorem k3167_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).1 1).2
      1040400725400229341768723519509895937525877805873695416866264402673946911013638244017762994).isSome = true := by
  decide +kernel

theorem k3167_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).2 1).1
      19136350095993053387948949374927043326798991069251017405937979656638145619456764346957687647719359099702843634).isSome = true := by
  decide +kernel

theorem k3167_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).1 3).2 2).2 3).2 1).2
      18675864343309648253710245540628023527605579896850684823742039649095467421773565732818516251228649629407804).isSome = true := by
  decide +kernel

theorem k3167_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).1 1).1
      269042139886333451266202688403292005199120244718238975951668191221657149726922968927709886643).isSome = true := by
  decide +kernel

theorem k3167_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).1 1).2
      89508536622348231741210915375066362023710191054520804912479205068028194748931542339114535267518686115633086331945458136843385650).isSome = true := by
  decide +kernel

theorem k3167_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).2 1).1 2).1
      865586035900909234071582253528266106927329054617747786610046254140).isSome = true := by
  decide +kernel

theorem k3167_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).2 1).1 2).2
      866309172144749596470961014745509770043828209075299161413454249020).isSome = true := by
  decide +kernel

theorem k3167_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).1 3).2 1).2
      19302236947854973926762000880877528128857711270028030081635877665881372053726123898674665319008013130905545906).isSome = true := by
  decide +kernel

theorem k3167_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).2 3).1 1).1
      263677656390131220185215561984040371134437433549313951320528730023367000086377848317246642).isSome = true := by
  decide +kernel

theorem k3167_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).2 3).1 1).2
      16465407814668461139134203521882777999717006865790585410644852245088742446951133779218226).isSome = true := by
  decide +kernel

theorem k3167_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).2 3).2 1).1
      16784162774449939307391251273372693249679305047302373427777373083268962965323860417927639282).isSome = true := by
  decide +kernel

theorem k3167_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).1 2).2 3).2 1).2
      65507010978522483799712419366637057798774096705251850608866627005015876482835405310865202).isSome = true := by
  decide +kernel

theorem k3167_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 3).1 1).1 2).1
      11679525426655793058644128506180118840023301180).isSome = true := by
  decide +kernel

theorem k3167_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 3).1 1).1 2).2
      862494228255726406655689817738986417060548577290490709856432798780).isSome = true := by
  decide +kernel

theorem k3167_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 3).1 1).2
      1042133789046901263047078984236061798065953447604832139558137305757287050259133941072624818).isSome = true := by
  decide +kernel

theorem k3167_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 3).2 1).1
      306772995776377228952629844861834947358843341176056176446454846387994596022740897038517332013729604334925089009).isSome = true := by
  decide +kernel

theorem k3167_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).1 3).2 1).2
      4055035188398184008299569112099473621703524447317472161285095707831876091788962243015228).isSome = true := by
  decide +kernel

theorem k3167_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).2 3).1 1).1
      66738319347310781607797302026773773041193652339892337426771260044901457710140147558971273459).isSome = true := by
  decide +kernel

theorem k3167_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).2 3).1 1).2
      1043388772123689683548795859777358316766208536779602022922350835462106892298266015181667506).isSome = true := by
  decide +kernel

theorem k3167_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).2 3).2 1).1
      299783455237868823855069457941055458765256668895116633477645954805024719709846996553568674124779159520001084).isSome = true := by
  decide +kernel

theorem k3167_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3167) 2).2 3).2 2).2 3).2 1).2
      4681377281229291193744855521362514807096613993976794301054072461574126047071385274338667436333107881950268).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3167 3168 :=
  (Cover.one (box := dirCellBox) (n := 3167)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3167_0) (.leaf _ k3167_1)) (.split 1 (.leaf _ k3167_2) (.leaf _ k3167_3))) (.split 2 (.split 1 (.leaf _ k3167_4) (.leaf _ k3167_5)) (.split 1 (.leaf _ k3167_6) (.leaf _ k3167_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3167_8) (.leaf _ k3167_9)) (.split 1 (.leaf _ k3167_10) (.leaf _ k3167_11))) (.split 2 (.split 1 (.leaf _ k3167_12) (.leaf _ k3167_13)) (.split 1 (.leaf _ k3167_14) (.leaf _ k3167_15))))) (.split 2 (.split 3 (.split 1 (.split 3 (.leaf _ k3167_16) (.leaf _ k3167_17)) (.leaf _ k3167_18)) (.split 1 (.leaf _ k3167_19) (.leaf _ k3167_20))) (.split 3 (.split 1 (.split 2 (.leaf _ k3167_21) (.leaf _ k3167_22)) (.leaf _ k3167_23)) (.split 1 (.leaf _ k3167_24) (.leaf _ k3167_25))))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3167_26) (.leaf _ k3167_27)) (.split 1 (.split 2 (.leaf _ k3167_28) (.leaf _ k3167_29)) (.leaf _ k3167_30))) (.split 3 (.split 1 (.leaf _ k3167_31) (.leaf _ k3167_32)) (.split 1 (.leaf _ k3167_33) (.leaf _ k3167_34)))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3167_35) (.leaf _ k3167_36)) (.leaf _ k3167_37)) (.split 1 (.leaf _ k3167_38) (.leaf _ k3167_39))) (.split 3 (.split 1 (.leaf _ k3167_40) (.leaf _ k3167_41)) (.split 1 (.leaf _ k3167_42) (.leaf _ k3167_43)))))))

end C4.Cert.Dir085
