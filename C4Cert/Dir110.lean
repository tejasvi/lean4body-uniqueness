module

public import C4Check

public section

/-! Cells `3530 ≤ n < 3531` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir110

theorem k3530_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).1 3).1
      4803440268211795209055527456812153951352695100679168497185652655501044643085991074467041714201626392214838).isSome = true := by
  decide +kernel

theorem k3530_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).1 3).2
      1007020421167842775770195632690920191249461482958792490847786682460351993678791407046).isSome = true := by
  decide +kernel

theorem k3530_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).2 3).1
      5702099466573847611736997261368781487820202555928340387432349164047226487690549208883268172038356946454724139295464870949017366).isSome = true := by
  decide +kernel

theorem k3530_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).1 2).2 3).2
      76211017816356891349558809249813163377805607828290630239637475479321139951484379450027466372263597822764489).isSome = true := by
  decide +kernel

theorem k3530_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).1
      22132001628329175177588831810556229311305470568504617317935458276077504724372285788216420758267464102073884844473467938258343063).isSome = true := by
  decide +kernel

theorem k3530_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).2 3).1
      295297544071166313132646557463585029765935372468050962072038169832522488333957925292480288238561021089225).isSome = true := by
  decide +kernel

theorem k3530_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).1 3).2 2).2 3).2
      248665762739322149978689134239887223243940868483991628919545021620688499004264772849).isSome = true := by
  decide +kernel

theorem k3530_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).1
      365980634927072629721342867186602277171656401170201290784903759315987175562896223033002381584833086909974275672330181241187289881).isSome = true := by
  decide +kernel

theorem k3530_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).1 3).2
      1667696541000278745162257112697715645695883953838404845513537272173661943077436711864368847718499933804416582906749339735837794298965923119212944841).isSome = true := by
  decide +kernel

theorem k3530_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).1
      1693116102526307531696408563161514031427818632919245046846549135642045359835923409397125202256415347063389141059435389579640744792450792172991765705).isSome = true := by
  decide +kernel

theorem k3530_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).1 2).2 3).2
      6690599259382956704468353425436843680424600147684094136600555294920389886691044233183132136110449501841002388484178868417117930665460065255062704921).isSome = true := by
  decide +kernel

theorem k3530_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).1 3).1
      74106162590893091684088756012502006494676106027641613451165645152698111754834551148765102397252153263561).isSome = true := by
  decide +kernel

theorem k3530_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).1 3).2
      3989328686779954042413189993031529245111896482790518296568137316462244355944178349297).isSome = true := by
  decide +kernel

theorem k3530_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).2 3).1
      4761417547069208287876482496783507927921168585300099195321959449121040493361242969567460257039619620750793).isSome = true := by
  decide +kernel

theorem k3530_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3530) 2).2 3).2 2).2 3).2
      18456318280030687477504822927860296149652667221222732559263178737256573296055925211684380058072170585521).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3530 3531 :=
  (Cover.one (box := dirCellBox) (n := 3530)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3530_0) (.leaf _ k3530_1)) (.split 3 (.leaf _ k3530_2) (.leaf _ k3530_3))) (.split 2 (.leaf _ k3530_4) (.split 3 (.leaf _ k3530_5) (.leaf _ k3530_6)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3530_7) (.leaf _ k3530_8)) (.split 3 (.leaf _ k3530_9) (.leaf _ k3530_10))) (.split 2 (.split 3 (.leaf _ k3530_11) (.leaf _ k3530_12)) (.split 3 (.leaf _ k3530_13) (.leaf _ k3530_14))))))

end C4.Cert.Dir110
