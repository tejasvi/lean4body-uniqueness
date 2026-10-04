module

public import C4Check

public section

/-! Cells `3226 ≤ n < 3233` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir093

theorem k3226_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).1 2).1 1).1
      250595305625005550850758636977309123884682557967307539996726673844978570022667215696444).isSome = true := by
  decide +kernel

theorem k3226_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).1 2).1 1).2
      62702085151380870816404270677588377108904636866614700231305095362064863961323239110204).isSome = true := by
  decide +kernel

theorem k3226_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).1 2).2 1).1
      250697991902514651351101314173902369010421542504043427666541729016020734247654087193148).isSome = true := by
  decide +kernel

theorem k3226_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).1 2).2 1).2
      250636308993430461261215899721539149273843339573428110432049563133481758289762570465852).isSome = true := by
  decide +kernel

theorem k3226_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).2 1).1 3).1
      3392449992035193804158457147311852190946906573375874386341486509116).isSome = true := by
  decide +kernel

theorem k3226_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).2 1).1 3).2
      52970115073399944932351204628559454556299185375794652849602149436).isSome = true := by
  decide +kernel

theorem k3226_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).2 1).2 3).1
      3391919576938826908882922041045464201064824125213787574605568789052).isSome = true := by
  decide +kernel

theorem k3226_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).1 3).2 1).2 3).2
      11483863868540453165461919457984408154612943420).isSome = true := by
  decide +kernel

theorem k3226_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).1 1).1 3).1
      3400869876607777399389068232430452016756716234658243929770102209596).isSome = true := by
  decide +kernel

theorem k3226_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).1 1).1 3).2
      3397548729557975113894359139081723741849391719942976515249262148668).isSome = true := by
  decide +kernel

theorem k3226_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).1 1).2 3).1
      3400192432957359621117816490488200058102488959920364549106726452284).isSome = true := by
  decide +kernel

theorem k3226_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).1 1).2 3).2
      3396861297469465892068365836045275913075027387505553648431184854076).isSome = true := by
  decide +kernel

theorem k3226_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).2 1).1 2).1
      3392705372782479511153786921221349890766422589584952677020510646844).isSome = true := by
  decide +kernel

theorem k3226_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).2 1).1 2).2
      848417832715306146926879536326028337476124512905449554993085267004).isSome = true := by
  decide +kernel

theorem k3226_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).2 1).2 2).1
      848079631889230554426755622861534096177258424176757108511469990460).isSome = true := by
  decide +kernel

theorem k3226_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3226) 2).2 3).2 1).2 2).2
      3393164894293410142178038310169273377589076700311490771414672667196).isSome = true := by
  decide +kernel

theorem k3227_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).1 3).1 1).1
      87090218981305129528483178103227184039424758936897241347425053579523838122650271344941031459316379332518582343243733084918510140).isSome = true := by
  decide +kernel

theorem k3227_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).1 3).1 1).2
      295335935293685639471870722208144360829028828023453428183617751346897539477521164376876184215348684896816700).isSome = true := by
  decide +kernel

theorem k3227_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).1 3).2 1).1
      4606189537922583531626103044422180273740074580407038918107510358904945238624095396343299074762441894654524).isSome = true := by
  decide +kernel

theorem k3227_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).1 3).2 1).2
      1151461848345896968489783898774708504516443485874212039016321408795212366960844153058860331633607257872956).isSome = true := by
  decide +kernel

theorem k3227_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).2 3).1 1).1
      1048865030142206908686169648854469489781461266803912938993901261590181908175535405383271565554).isSome = true := by
  decide +kernel

theorem k3227_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).2 3).1 1).2
      65520854064562504106798426617859308443616779166466949034787166268716702362337873399737993459).isSome = true := by
  decide +kernel

theorem k3227_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).2 3).2 1).1
      3996540911830727570280575028392114913964746081637581662763210651131372988713011900052028).isSome = true := by
  decide +kernel

theorem k3227_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3227) 2).2 3).2 1).2
      3996278347247458863608565069106834295118565100763589036154022066678109782698857443871292).isSome = true := by
  decide +kernel

theorem k3228_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).1 3).1 1).1
      52885697299066690501682519258604390873056088412956350148302467644).isSome = true := by
  decide +kernel

theorem k3228_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).1 3).1 1).2
      974634641646329493964841965606162856994471966532716695387214688102728978065942509116).isSome = true := by
  decide +kernel

theorem k3228_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).1 3).2 1).1
      52802750548804122672635550655884989848079392735392213903604052540).isSome = true := by
  decide +kernel

theorem k3228_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).1 3).2 1).2
      243514199377052913327059312220292550750734858432823090972518248388407174415034973612).isSome = true := by
  decide +kernel

theorem k3228_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).2 3).1 1).1
      62456983317589938635991776443727973144292511959029591343330087680640165773577490461244).isSome = true := by
  decide +kernel

theorem k3228_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).2 3).1 1).2
      62391730277842668107500368498701697123885417330761900704147344854621835278477602835004).isSome = true := by
  decide +kernel

theorem k3228_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).2 3).2 1).1
      52817265267725432669529723559287647389123056571083105962949997116).isSome = true := by
  decide +kernel

theorem k3228_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3228) 2).2 3).2 1).2
      211249397951653647149782326568702062042925196225483428167314557500).isSome = true := by
  decide +kernel

theorem k3229_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3229) 2).1 3).1
      21203722577906689900120846681207861547532285006320549780704152698034727217596705263088664762142954374652678632094921250332081).isSome = true := by
  decide +kernel

theorem k3229_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3229) 2).1 3).2
      21195372554006063007212680976307198453243711593491255571081560141404573921846488201167389690521100038537568066252944859946417).isSome = true := by
  decide +kernel

theorem k3229_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3229) 2).2 3).1 1).1
      52788850029643837354515684308011475480215396235713954000992072252).isSome = true := by
  decide +kernel

theorem k3229_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3229) 2).2 3).1 1).2
      211142073145050114614482765488167189331515596671331054802076944956).isSome = true := by
  decide +kernel

theorem k3229_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3229) 2).2 3).2
      339185663887348507675375380652549324972167137409645915526982498990822267976516240731823429942128676087954918035538791500184753).isSome = true := by
  decide +kernel

theorem k3230_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3230) 2).1 3).1
      1148641767674050156462817157866786155428671160272929019462528071994382435941055749157249583023063335652156).isSome = true := by
  decide +kernel

theorem k3230_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3230) 2).1 3).2
      60793374472526699113386492278249137080235896231860039146555552335081661283537413553).isSome = true := by
  decide +kernel

theorem k3230_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3230) 2).2 3).1
      1148788020842859020764704635551657417277371358422648845306098127857345397072825115337890950498947486604465).isSome = true := by
  decide +kernel

theorem k3230_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3230) 2).2 3).2
      71813802814491481198913520567848549758309453235907613588908166495929731053015656336978452189326872016444).isSome = true := by
  decide +kernel

theorem k3231_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3231) 2).1
      84694915852223687524773704156079628344717258559896878936689105111768011308568748713506781115306600917050037645696584476882163).isSome = true := by
  decide +kernel

theorem k3231_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3231) 2).2 3).1
      62241682401658952198084548627259383608043429263897885082260372586583670296918491493581).isSome = true := by
  decide +kernel

theorem k3231_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3231) 2).2 3).2
      823592608987053063791093318214229330374838593890148140354467052).isSome = true := by
  decide +kernel

theorem k3232_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3232) 2).1
      15188005258832769299624409902473606719829656146948665249861026191661690194057837937).isSome = true := by
  decide +kernel

theorem k3232_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3232) 2).2
      84672107882783821031060552022298225250756759856302921669357908632580878011411346015899994840519965600185296206436401655149811).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3226 3233 :=
  (Cover.one (box := dirCellBox) (n := 3226)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3226_0) (.leaf _ k3226_1)) (.split 1 (.leaf _ k3226_2) (.leaf _ k3226_3))) (.split 1 (.split 3 (.leaf _ k3226_4) (.leaf _ k3226_5)) (.split 3 (.leaf _ k3226_6) (.leaf _ k3226_7)))) (.split 3 (.split 1 (.split 3 (.leaf _ k3226_8) (.leaf _ k3226_9)) (.split 3 (.leaf _ k3226_10) (.leaf _ k3226_11))) (.split 1 (.split 2 (.leaf _ k3226_12) (.leaf _ k3226_13)) (.split 2 (.leaf _ k3226_14) (.leaf _ k3226_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3227)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3227_0) (.leaf _ k3227_1)) (.split 1 (.leaf _ k3227_2) (.leaf _ k3227_3))) (.split 3 (.split 1 (.leaf _ k3227_4) (.leaf _ k3227_5)) (.split 1 (.leaf _ k3227_6) (.leaf _ k3227_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3228)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3228_0) (.leaf _ k3228_1)) (.split 1 (.leaf _ k3228_2) (.leaf _ k3228_3))) (.split 3 (.split 1 (.leaf _ k3228_4) (.leaf _ k3228_5)) (.split 1 (.leaf _ k3228_6) (.leaf _ k3228_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3229)
      (.split 2 (.split 3 (.leaf _ k3229_0) (.leaf _ k3229_1)) (.split 3 (.split 1 (.leaf _ k3229_2) (.leaf _ k3229_3)) (.leaf _ k3229_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3230)
      (.split 2 (.split 3 (.leaf _ k3230_0) (.leaf _ k3230_1)) (.split 3 (.leaf _ k3230_2) (.leaf _ k3230_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3231)
      (.split 2 (.leaf _ k3231_0) (.split 3 (.leaf _ k3231_1) (.leaf _ k3231_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3232)
      (.split 2 (.leaf _ k3232_0) (.leaf _ k3232_1)))

end C4.Cert.Dir093
