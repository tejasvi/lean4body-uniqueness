module

public import C4Check

public section

/-! Cells `3615 ≤ n < 3617` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir114

theorem k3615_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).1 3).1 2).1
      64529003060810585954895139411621984062679805051820009519177355825509500931566488360753).isSome = true := by
  decide +kernel

theorem k3615_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).1 3).1 2).2
      4031331118306227209559670732962924962508876689769733203527196903292856670231772747569).isSome = true := by
  decide +kernel

theorem k3615_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).1 3).2 2).1
      75797348145262781974366170000109722037580122809540270596893270261353258268305136208987795623320382404664113).isSome = true := by
  decide +kernel

theorem k3615_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).1 3).2 2).2
      256960905214356696785451804721538361896185534564086391575711659580196459246932508367665).isSome = true := by
  decide +kernel

theorem k3615_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).2 3).1
      1439354075079145427007587707635209421491039159852966934458145186457040748448731091243503441563999155093480752350077860253109973234).isSome = true := by
  decide +kernel

theorem k3615_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).2 3).2 2).1
      4013134557931594403627487657572012660628512875488607342728868760586953409507084621617).isSome = true := by
  decide +kernel

theorem k3615_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).1 2).2 3).2 2).2
      250749196686269475986653944166856743570307301436922102272593744056292804895901703980).isSome = true := by
  decide +kernel

theorem k3615_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).1 2).1 3).1
      75470371830758115358892332999649817070439527280786910023749669886942029890213774560194465968967869078018865).isSome = true := by
  decide +kernel

theorem k3615_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).1 2).1 3).2
      16304304291147683485121306131662003898515720119140762005292565112938826785372107778399025).isSome = true := by
  decide +kernel

theorem k3615_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).1 2).2 3).1
      75518528564160529786877566210930828730796006734644981116497723773335247412188037227149288025852369924627249).isSome = true := by
  decide +kernel

theorem k3615_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).1 2).2 3).2
      75241886083559075256716184010494150863968924219135858281245095670962667179829837841426063046921637946825521).isSome = true := by
  decide +kernel

theorem k3615_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).2 2).1 1).1
      255199249463418747417818061446736784930263904420110934763941570426868423109919778626355).isSome = true := by
  decide +kernel

theorem k3615_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).2 2).1 1).2
      75283923436244384893389670152155760513164678228157829386167442614418999016596359463827814380441694479948595).isSome = true := by
  decide +kernel

theorem k3615_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).2 2).2 1).1
      15957078372152097055225823561287057563101572376210648547660234597496276640838617110323).isSome = true := by
  decide +kernel

theorem k3615_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3615) 3).2 2).2 2).2 1).2
      15961675737839084381681900340865250070632142360285561138492764549279961716034166017740).isSome = true := by
  decide +kernel

theorem k3616_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).1 2).1 3).1
      1015776360318479169943291157979411835543455324946157539628557409652967560252519254694705).isSome = true := by
  decide +kernel

theorem k3616_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).1 2).1 3).2
      1013003433429661000061815517865684959114499972804814575965295993152520973261842315320113).isSome = true := by
  decide +kernel

theorem k3616_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).1 2).2 1).1
      1014165579807241611300402777832493028043885626872519559774625489088118401562195674897203).isSome = true := by
  decide +kernel

theorem k3616_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).1 2).2 1).2
      1013692423224696615345825023755534254597667344375158641343014258455537860609722953603891).isSome = true := by
  decide +kernel

theorem k3616_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).2 2).1 3).1
      1010631236561128162990497002802611732001685907894714033383595347124035519799660237134641).isSome = true := by
  decide +kernel

theorem k3616_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).2 2).1 3).2
      1008606911087306598400989829770744155650375285853665060487263416103551395903141647850289).isSome = true := by
  decide +kernel

theorem k3616_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).2 2).2 1).1
      1009590972473845466281981391189775451938113987467728825561283556090449793212511931964211).isSome = true := by
  decide +kernel

theorem k3616_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).2 2).2 1).2
      1009223086648152646211580206439711316576512634103918402272749322594614183249748495538995).isSome = true := by
  decide +kernel

theorem k3616_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).1 2).1 1).1
      1014746643501215223845613255503347790242495616066109241656717989045105872928287171910451).isSome = true := by
  decide +kernel

theorem k3616_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).1 2).1 1).2
      74842238978894362546962240677685077905689911888104850430066332649537088167555934754911559949243484676152115).isSome = true := by
  decide +kernel

theorem k3616_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).1 2).2 1).1
      63539324860781954055996019199642039294639603138275880434876781198743468953653441559244).isSome = true := by
  decide +kernel

theorem k3616_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).1 2).2 1).2
      1014831854436723825269843872755275003634944157921229406647488393150957485304630200343347).isSome = true := by
  decide +kernel

theorem k3616_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).2 2).1 1).1
      1010169107091144616802465348782170313793198846179673190139240190799043531991525466676019).isSome = true := by
  decide +kernel

theorem k3616_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).2 2).1 1).2
      1010944302243837015275407972741878822665563359868589167870816219868151784798107337857842).isSome = true := by
  decide +kernel

theorem k3616_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).2 2).2 1).1
      1010688767629667981062660107540820392283695161376634574515484709820970475585312424041267).isSome = true := by
  decide +kernel

theorem k3616_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).2 2).2 1).2
      3428924351803740342711407698133880554495160249583539280766931119820).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3615 3617 :=
  (Cover.one (box := dirCellBox) (n := 3615)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3615_0) (.leaf _ k3615_1)) (.split 2 (.leaf _ k3615_2) (.leaf _ k3615_3))) (.split 3 (.leaf _ k3615_4) (.split 2 (.leaf _ k3615_5) (.leaf _ k3615_6)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3615_7) (.leaf _ k3615_8)) (.split 3 (.leaf _ k3615_9) (.leaf _ k3615_10))) (.split 2 (.split 1 (.leaf _ k3615_11) (.leaf _ k3615_12)) (.split 1 (.leaf _ k3615_13) (.leaf _ k3615_14)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3616)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3616_0) (.leaf _ k3616_1)) (.split 1 (.leaf _ k3616_2) (.leaf _ k3616_3))) (.split 2 (.split 3 (.leaf _ k3616_4) (.leaf _ k3616_5)) (.split 1 (.leaf _ k3616_6) (.leaf _ k3616_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k3616_8) (.leaf _ k3616_9)) (.split 1 (.leaf _ k3616_10) (.leaf _ k3616_11))) (.split 2 (.split 1 (.leaf _ k3616_12) (.leaf _ k3616_13)) (.split 1 (.leaf _ k3616_14) (.leaf _ k3616_15))))))

end C4.Cert.Dir114
