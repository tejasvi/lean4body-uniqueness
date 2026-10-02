module

public import C4Check

public section

/-! Cells `2944 ≤ n < 2972` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir078

theorem k2944_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2944) 3).1
      62170554018496472306936656326523382866172694101316258754917561420214993914147578438).isSome = true := by
  decide +kernel

theorem k2944_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2944) 3).2
      345176418986369726096973323114809203852116312043341617440518147413171592342709155761022540340143496162015867103164952875463922).isSome = true := by
  decide +kernel

theorem k2945_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2945) 2).1
      6481670035704371008911863457223558611357747641614712885894795358813836502435902600419353395836712726987854938527317622696163290946614807727627662579).isSome = true := by
  decide +kernel

theorem k2945_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2945) 2).2
      343143304939167920400201644695453646397130239161652641787115389744068100191515663945245778205535594901994707950708149261530355).isSome = true := by
  decide +kernel

theorem k2946_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2946) 2).1
      5603895365730881408990016317794894572578015269742908003684971984092512605439122321750913258729187096162101116653645604164955259708).isSome = true := by
  decide +kernel

theorem k2946_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2946) 2).2
      303786224912216275723270972905624540486456192837037925926360740904387275060188419353530009460244471762726667068).isSome = true := by
  decide +kernel

theorem k2947_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2947) 3).1
      87353432190222257329039701869762092388218915190055150992385290495942577806929488249866051899695383374279351497215690382021477180).isSome = true := by
  decide +kernel

theorem k2947_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2947) 3).2
      4728994525637682858118378875879858051405227023862170986361767663520723925579754106415633556264650070492693308).isSome = true := by
  decide +kernel

theorem k2948_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2948) 3).1
      4724069501929230054262728477318852758830552994271197264434766896368400906647205495706619417336518646325822268).isSome = true := by
  decide +kernel

theorem k2948_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2948) 3).2
      255829976717985878738672578360208896383285363738858148914130703650271045783528094158093372).isSome = true := by
  decide +kernel

theorem k2949_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2949) 3).1
      255652359226802899791299430864701086159120226137638467079194104088686086519897891009526844).isSome = true := by
  decide +kernel

theorem k2949_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2949) 3).2
      3991627440346399884200224277786293542158552347967207242782846547286077627871856933682236).isSome = true := by
  decide +kernel

theorem k2950_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2950) 1).1
      997052435818091172938226890155220219194595904844857833058681521885224821738063279635516).isSome = true := by
  decide +kernel

theorem k2950_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2950) 1).2
      216214133680994419500131738522162109619852097513481061809428765031484).isSome = true := by
  decide +kernel

theorem k2951_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2951) 3).1
      15942778252360273729340748823847210464108083668679592842917912490213019949747989927115836).isSome = true := by
  decide +kernel

theorem k2951_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2951) 3).2
      52733361651894003158113290019555644766250919057046482721408105532).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 2952 2953 [
    5551121328469892747073484143331986142276057109319302368761267104521696440249000268153445619652101700621967108456340238300162802492] = true := by
  decide +kernel

theorem c9 : allCells dirCell 2953 2954 [
    15551210070685809115524784582728324120437955059559462247326157081184001690619258323772] = true := by
  decide +kernel

theorem c10 : allCells dirCell 2954 2955 [
    286777093655918930772978103821750117779408515099744345843932908496883741861059070392902654291208268403516] = true := by
  decide +kernel

theorem c11 : allCells dirCell 2955 2972 [
    51427137519761684849474413104848349897857914423302427081854673, 147547515966328869204, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2944 2972 :=
  (Cover.one (box := dirCellBox) (n := 2944)
      (.split 3 (.leaf _ k2944_0) (.leaf _ k2944_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2945)
      (.split 2 (.leaf _ k2945_0) (.leaf _ k2945_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2946)
      (.split 2 (.leaf _ k2946_0) (.leaf _ k2946_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2947)
      (.split 3 (.leaf _ k2947_0) (.leaf _ k2947_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2948)
      (.split 3 (.leaf _ k2948_0) (.leaf _ k2948_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2949)
      (.split 3 (.leaf _ k2949_0) (.leaf _ k2949_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2950)
      (.split 1 (.leaf _ k2950_0) (.leaf _ k2950_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2951)
      (.split 3 (.leaf _ k2951_0) (.leaf _ k2951_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11)

end C4.Cert.Dir078
