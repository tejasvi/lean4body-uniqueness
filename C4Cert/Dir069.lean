module

public import C4Check

public section

/-! Cells `2806 ≤ n < 2830` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir069

theorem k2806_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).1 1).1
      978065316094998145199089544276723060816990843191761283946264446305796431044583193660).isSome = true := by
  decide +kernel

theorem k2806_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).1 1).2
      212019330870697562468371103935422949776279643441418353038516941372).isSome = true := by
  decide +kernel

theorem k2806_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).2 1).1
      976682443739577205245897829375103777259695884456534893384229814548911655358476155964).isSome = true := by
  decide +kernel

theorem k2806_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).1 3).2 1).2
      211738091604504840494940877509567083324148463649322632751628143164).isSome = true := by
  decide +kernel

theorem k2806_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).1 1).1
      212272888608831756559806542965937283199199492010180327878820723772).isSome = true := by
  decide +kernel

theorem k2806_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2806) 2).2 3).1 1).2
      53049192725984813816156195497794442397803098985539545872936071740).isSome = true := by
  decide +kernel

theorem k2806_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2806) 2).2 3).2
      25731535037469267014298912094305559004958360636129892095440781519657771899127956168957275591263236145793733575201043959316388769174370643478677758780).isSome = true := by
  decide +kernel

theorem k2807_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2807) 2).1 3).1
      339982746770804088742362019922959616277299738203556547186470214887333341320392127486435822326297385892867701781429000283217073).isSome = true := by
  decide +kernel

theorem k2807_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2807) 2).1 3).2
      4603781060874702239500214450793251202994647016178594025876143384139527920894813111184162540859918364275377).isSome = true := by
  decide +kernel

theorem k2807_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2807) 2).2 3).1
      25700200717417223518963631300813191508983961283589234637564813693051810701541853346015303490991854671705172260007723470090566299522980640565260919612).isSome = true := by
  decide +kernel

theorem k2807_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2807) 2).2 3).2
      249645873715400048093454534422681019595455660752959583734739671119868753512201417378364).isSome = true := by
  decide +kernel

theorem k2808_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2808) 2).1 3).1
      287560965385914786297240322634154722211974243865942203541490651105333708756281630646580489186769645327164).isSome = true := by
  decide +kernel

theorem k2808_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2808) 2).1 3).2
      15215686501234364249472507321164063958047404093913130421096783323075520362175815025).isSome = true := by
  decide +kernel

theorem k2808_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2808) 2).2 3).1
      15591493031211083844852559731334722778156474576887104303308008382746063921836159650364).isSome = true := by
  decide +kernel

theorem k2808_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2808) 2).2 3).2
      71870227281529373953173679433521667990684629791107024277195373184537869734217654402757862750651048916540).isSome = true := by
  decide +kernel

theorem k2809_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2809) 2).1
      84758825236244484911806409620611922561843352522106227410343776974976005835437795793167609804572591672442843680839877297796339).isSome = true := by
  decide +kernel

theorem k2809_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2809) 2).2
      1601370714522712712412796357630997344002336201518402444649980252600571673911739540459367450994842381673227444092144335462385060927109071958287938247).isSome = true := by
  decide +kernel

theorem k2810_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2810) 2).1
      60788183447451612510110346668695305553256464462861309996365660003237918070691849293).isSome = true := by
  decide +kernel

theorem k2810_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2810) 2).2
      84719837936256363493677129421302897827806232698547895001919696563441378728589545390644634794837706826356897413355757167801587).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2811 2828 [
    21173635639380646354533086847012099625146740824581375069539162560164624479519135202888166116262832805436565229696958245302598,
    11157018025255379119398278025458712570967106, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2828 2830 [
    0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2806 2830 :=
  (Cover.one (box := dirCellBox) (n := 2806)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2806_0) (.leaf _ k2806_1)) (.split 1 (.leaf _ k2806_2) (.leaf _ k2806_3))) (.split 3 (.split 1 (.leaf _ k2806_4) (.leaf _ k2806_5)) (.leaf _ k2806_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2807)
      (.split 2 (.split 3 (.leaf _ k2807_0) (.leaf _ k2807_1)) (.split 3 (.leaf _ k2807_2) (.leaf _ k2807_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2808)
      (.split 2 (.split 3 (.leaf _ k2808_0) (.leaf _ k2808_1)) (.split 3 (.leaf _ k2808_2) (.leaf _ k2808_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2809)
      (.split 2 (.leaf _ k2809_0) (.leaf _ k2809_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2810)
      (.split 2 (.leaf _ k2810_0) (.leaf _ k2810_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6)

end C4.Cert.Dir069
