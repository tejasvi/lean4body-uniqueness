module

public import C4Check

public section

/-! Cells `3170 ≤ n < 3195` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir087

theorem k3170_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).1 3).1 2).1
      85019023988459198890233488810711550334228507821809562069062003477766455998919755503989875939833644573175275115346423936546033).isSome = true := by
  decide +kernel

theorem k3170_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).1 3).1 2).2
      1360888878219861409464115731285101056591523055187985833151758058955087237778044802835439737556115271857917048256605995148342513).isSome = true := by
  decide +kernel

theorem k3170_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).1 3).2 2).1
      15241591320236642452742047131022076276578530799731331863789696900037039568841498993).isSome = true := by
  decide +kernel

theorem k3170_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).1 3).2 2).2
      21247062558411721993198039726536269553732980830023765665719131623629400741084041260568209460931153285105860627215870671549681).isSome = true := by
  decide +kernel

theorem k3170_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).1 2).1 1).1
      3907231169173273912710595655794253388620684593516892811138822846364134813972685116332).isSome = true := by
  decide +kernel

theorem k3170_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).1 2).1 1).2
      61043025693849044687085783425955807714084219714262799502004108110494511866359174972).isSome = true := by
  decide +kernel

theorem k3170_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).1 2).2 1).1
      977109889331911334222678291034338925812424420234829488973378281225215435880295429356).isSome = true := by
  decide +kernel

theorem k3170_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).1 2).2 1).2
      3908026313453415472415969666000667716626030108550318320381181967205045627236675737404).isSome = true := by
  decide +kernel

theorem k3170_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).2 2).1
      339973743884672788602214031178355890733852911956137495589016244491766616483682065936520961603900258953354258042073458376013041).isSome = true := by
  decide +kernel

theorem k3170_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).2 2).2
      340044412801557994467897891105322088481429313155810294370116009605800516594342628754635391106522341168070159066230679862867185).isSome = true := by
  decide +kernel

theorem k3171_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3171) 2).1
      31011969441756438383488045862467038556520871743047379897257191656753490310926727065764769954448053306901275172441076670213794600296124854146982554291968060750126468773344542).isSome = true := by
  decide +kernel

theorem k3171_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3171) 2).2 3).1 1).1
      287833309606791658299344214274840359315430999950881902535129145783193719421513257738046646105834474329330).isSome = true := by
  decide +kernel

theorem k3171_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3171) 2).2 3).1 1).2
      71948278250183980632038871693959627695259331074310860974400369371759472818093760738084087378301838085490).isSome = true := by
  decide +kernel

theorem k3171_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3171) 2).2 3).2
      1848646529519723814711103385477695375164187747072672456431214357591528228624488784752641462401260445807231451334784530375040449592133561514147490482268333591401719241).isSome = true := by
  decide +kernel

theorem k3172_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3172) 2).1
      490759217848935645877175506441823366290961158).isSome = true := by
  decide +kernel

theorem k3172_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3172) 2).2 2).1
      60850405807834805890565529762504604638178376952863569318503370960226272202891811399).isSome = true := by
  decide +kernel

theorem k3172_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3172) 2).2 2).2
      71837288992942842672459237824406883808395292987394517514428200912923884282614043011586063087531125568967).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3173 3193 [
    6196350484188188879290779398, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3193_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3193) 3).1
      1).isSome = true := by
  decide +kernel

theorem k3193_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3193) 3).2 3).1
      322344805461326120445534033950).isSome = true := by
  decide +kernel

theorem k3193_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3193) 3).2 3).2 2).1
      32096081506782352900604920955013304319218664116649931191400850005413422674429071325795765754920081858045704640429672625045920407766121508705193881435775641690016772377).isSome = true := by
  decide +kernel

theorem k3193_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3193) 3).2 3).2 2).2
      771948611079416354309702233193154975644586055).isSome = true := by
  decide +kernel

theorem k3194_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).1 1).1
      419714172567704643172023509039277418108725330550711463727757511029096217877190092859959053646040417412768486822244462308412940914065707888637426).isSome = true := by
  decide +kernel

theorem k3194_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).1 1).2
      90602408837677311144771037016301207546794514843700826341025179150100852296527926753581670503537539835322576549444647675327730).isSome = true := by
  decide +kernel

theorem k3194_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).2 1).1 2).1
      76063684139171976992505754336342159836543962525535728548244939279612724464392372454019724671770332485436).isSome = true := by
  decide +kernel

theorem k3194_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).2 1).1 2).2
      218274190469005282917521070497020402844436870535318796630711612).isSome = true := by
  decide +kernel

theorem k3194_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).1 3).2 1).2
      1690940134297510649656511241601861064136762788790854769852251971797459418282474136221896219923057025807142471566662610779754500387996213412674130866).isSome = true := by
  decide +kernel

theorem k3194_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).2 3).1
      22650040829353375399584962003573055629250117222234517288402203159529496261351975891821805716775275081004277621468296973166025).isSome = true := by
  decide +kernel

theorem k3194_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).2 3).2 1).1
      76192620326672811624880733121106153290068939591772035959147188384011781054368623565534885105494984586482).isSome = true := by
  decide +kernel

theorem k3194_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).1 2).2 3).2 1).2
      19007327391585762313170032415282101115774799321297336499934146106329489497492198332955353481632562503090).isSome = true := by
  decide +kernel

theorem k3194_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).1 1).1 2).1
      4079639270363869680373157345568251971271680761159467113322222669896641251109028483900).isSome = true := by
  decide +kernel

theorem k3194_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).1 1).1 2).2
      1021888957691854286846068173156362714695865926541387991403918420528537363355412067564).isSome = true := by
  decide +kernel

theorem k3194_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).1 1).2 2).1
      3451987093548855265261435270927307049795903800054152932309229356).isSome = true := by
  decide +kernel

theorem k3194_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).1 1).2 2).2
      55392030789238821118646602357906629762981377584378097792455144108).isSome = true := by
  decide +kernel

theorem k3194_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).2 2).1 1).1
      4144954809954673489576853828638667417764018815134130209590062727663085777288778143359666).isSome = true := by
  decide +kernel

theorem k3194_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).2 2).1 1).2
      259085602049863422734762303009197201621045478211187197569369651617220889183634940861234).isSome = true := by
  decide +kernel

theorem k3194_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).2 2).2 1).1
      253703661356677823059689689973237978554073704463493797781555602623473315636080901548).isSome = true := by
  decide +kernel

theorem k3194_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).1 3).2 2).2 1).2
      3428812303661825163492090411056857889743184460275994141366050604).isSome = true := by
  decide +kernel

theorem k3194_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).1 1).1
      88965024899552391769440121605398618813110870923097289543245712708863201601999615551565469533304316574080605041564040531113202).isSome = true := by
  decide +kernel

theorem k3194_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).1 1).2
      22281371791567397468801452920111506794870451787503600674564585514274556500560794175340700264042666138216190916862853552364978).isSome = true := by
  decide +kernel

theorem k3194_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).2 1).1
      104431030663377696917996623793182901346131893703189937600845226136098861081928938173073474481561250789317804207597014069466429768747841137469159090).isSome = true := by
  decide +kernel

theorem k3194_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3194) 3).2 2).2 3).2 1).2
      306635033992276094250108151608619733468464469339011408267723525909106735851518373338905056756954549165063346).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3170 3195 :=
  (Cover.one (box := dirCellBox) (n := 3170)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3170_0) (.leaf _ k3170_1)) (.split 2 (.leaf _ k3170_2) (.leaf _ k3170_3))) (.split 3 (.split 2 (.split 1 (.leaf _ k3170_4) (.leaf _ k3170_5)) (.split 1 (.leaf _ k3170_6) (.leaf _ k3170_7))) (.split 2 (.leaf _ k3170_8) (.leaf _ k3170_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3171)
      (.split 2 (.leaf _ k3171_0) (.split 3 (.split 1 (.leaf _ k3171_1) (.leaf _ k3171_2)) (.leaf _ k3171_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3172)
      (.split 2 (.leaf _ k3172_0) (.split 2 (.leaf _ k3172_1) (.leaf _ k3172_2)))).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 3193)
      (.split 3 (.leaf _ k3193_0) (.split 3 (.leaf _ k3193_1) (.split 2 (.leaf _ k3193_2) (.leaf _ k3193_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3194)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3194_0) (.leaf _ k3194_1)) (.split 1 (.split 2 (.leaf _ k3194_2) (.leaf _ k3194_3)) (.leaf _ k3194_4))) (.split 3 (.leaf _ k3194_5) (.split 1 (.leaf _ k3194_6) (.leaf _ k3194_7)))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3194_8) (.leaf _ k3194_9)) (.split 2 (.leaf _ k3194_10) (.leaf _ k3194_11))) (.split 2 (.split 1 (.leaf _ k3194_12) (.leaf _ k3194_13)) (.split 1 (.leaf _ k3194_14) (.leaf _ k3194_15)))) (.split 3 (.split 1 (.leaf _ k3194_16) (.leaf _ k3194_17)) (.split 1 (.leaf _ k3194_18) (.leaf _ k3194_19))))))

end C4.Cert.Dir087
