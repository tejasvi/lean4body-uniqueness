module

public import C4Check

public section

/-! Cells `3195 ≤ n < 3196` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir088

theorem k3195_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).1 2).1 1).1
      64443976987495338139981435657474314484062028778842700889189863730148593182374924516524).isSome = true := by
  decide +kernel

theorem k3195_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).1 2).1 1).2
      1030320027362450364547815206499921422626229395099831776473885514363303465708555871940396).isSome = true := by
  decide +kernel

theorem k3195_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).1 2).2 1).1
      3497635147295749847565082139903073102095753502870065764752739005100).isSome = true := by
  decide +kernel

theorem k3195_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).1 2).2 1).2
      4029498297790037297287232323718063124128228483101541123253141491740892715859093974828).isSome = true := by
  decide +kernel

theorem k3195_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).2 2).1 1).1
      1025472485106040715441177375995904151883937383174323494063027979232837223742368328184380).isSome = true := by
  decide +kernel

theorem k3195_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).2 2).1 1).2
      256194862036545674678406606652868772143883168657179698079155357544215346897906086407884).isSome = true := by
  decide +kernel

theorem k3195_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).2 2).2 1).1
      64169421959419794434437860295444307677141620719520849732409057030356211347484782754988).isSome = true := by
  decide +kernel

theorem k3195_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).2 2).2 1).2
      1001971323407757309722232040561391092447377953205933454273787279025324913238913440716).isSome = true := by
  decide +kernel

theorem k3195_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 3).1 2).1 1).1
      54706754884891636883077668728589604151239944425544361135502359980).isSome = true := by
  decide +kernel

theorem k3195_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 3).1 2).1 1).2
      3416535400660397742154215143777956975461642185852186839980859180).isSome = true := by
  decide +kernel

theorem k3195_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 3).1 2).2
      415148154114518677868175834059534450610995375168335564486144763003305822583088800449162299366118939685879193610094711020700581865389146418929040817).isSome = true := by
  decide +kernel

theorem k3195_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 3).2 2).1
      19400484645866476431643201660697606739504720247385915821654519936201993401826892002588760977383268635046703793).isSome = true := by
  decide +kernel

theorem k3195_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 3).2 2).2
      77669805333896492198684718375097031209428119072739496993439306444388551930459638214667987947580773097437262513).isSome = true := by
  decide +kernel

theorem k3195_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).1 3).1 1).1
      255207638020819505589818675655914208028928109504530531851665476381611006925615605988412).isSome = true := by
  decide +kernel

theorem k3195_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).1 3).1 1).2
      15940363964961470631618255926235161708316394891361021995650325180196429630689370402508).isSome = true := by
  decide +kernel

theorem k3195_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).1 3).2 1).1
      13781207808239126726286935795215192655253529615094505213383031569468).isSome = true := by
  decide +kernel

theorem k3195_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).1 3).2 1).2
      15880835143320581351657718320588206682934826782364411835775432972136034999900722543676).isSome = true := by
  decide +kernel

theorem k3195_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).2 3).1 1).1
      13849426257700831420104472651641330320550440618072277654051321216060).isSome = true := by
  decide +kernel

theorem k3195_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).2 3).1 1).2
      216272614974366796294038744719305868968324465550116215330034797516).isSome = true := by
  decide +kernel

theorem k3195_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).2 3).2 1).1
      862291262880259530638864616189565167970411348647876139180040764476).isSome = true := by
  decide +kernel

theorem k3195_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).2 3).2 1).2
      215453001344537190202689877451046396420164843751391590298748832716).isSome = true := by
  decide +kernel

theorem k3195_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 3).1 2).1
      77254062759896699657236394259262167713054111363198580101008131668822088946558323478666289784310589600290946225).isSome = true := by
  decide +kernel

theorem k3195_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 3).1 2).2
      1208198690745620344370638698162915346375880925259862197081849070622312893710492604602334478724488759610014897).isSome = true := by
  decide +kernel

theorem k3195_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 3).2 2).1 1).1
      863135093274703918054524811866003982108252552739449891033773358140).isSome = true := by
  decide +kernel

theorem k3195_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 3).2 2).1 1).2
      13480099948017947036120863931501207233228888217048685850184481484).isSome = true := by
  decide +kernel

theorem k3195_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 3).2 2).2
      19256554597933112155602550144824449809371669216448661580900387991141503787041942888297753047368259378172260593).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3195 3196 :=
  (Cover.one (box := dirCellBox) (n := 3195)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3195_0) (.leaf _ k3195_1)) (.split 1 (.leaf _ k3195_2) (.leaf _ k3195_3))) (.split 2 (.split 1 (.leaf _ k3195_4) (.leaf _ k3195_5)) (.split 1 (.leaf _ k3195_6) (.leaf _ k3195_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3195_8) (.leaf _ k3195_9)) (.leaf _ k3195_10)) (.split 2 (.leaf _ k3195_11) (.leaf _ k3195_12)))) (.split 2 (.split 2 (.split 3 (.split 1 (.leaf _ k3195_13) (.leaf _ k3195_14)) (.split 1 (.leaf _ k3195_15) (.leaf _ k3195_16))) (.split 3 (.split 1 (.leaf _ k3195_17) (.leaf _ k3195_18)) (.split 1 (.leaf _ k3195_19) (.leaf _ k3195_20)))) (.split 3 (.split 2 (.leaf _ k3195_21) (.leaf _ k3195_22)) (.split 2 (.split 1 (.leaf _ k3195_23) (.leaf _ k3195_24)) (.leaf _ k3195_25))))))

end C4.Cert.Dir088
