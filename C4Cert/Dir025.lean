module

public import C4Check

public section

/-! Cells `2020 ≤ n < 2023` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir025

theorem k2020_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).1 3).1
      62039997957065490042838127001646985740154589676096683195959970285337183473176726545).isSome = true := by
  decide +kernel

theorem k2020_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2020) 3).1 2).1 3).2
      18260734499467635351380686507743777377459811142926264402909914615189753684647051587217866466939490841969).isSome = true := by
  decide +kernel

theorem k2020_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2020) 3).1 2).2
      6375257681730002876367010852953609000691734186523370845017644875871495686608417498960325487889981235977008185245625845964938080895570314263595847).isSome = true := by
  decide +kernel

theorem k2020_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).1 3).1
      18217001191174072581286780984882652092264081207464621036725688179911848736345057591669769195966920079729).isSome = true := by
  decide +kernel

theorem k2020_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).1 3).2
      3940306406923706938113749655082146078143506411065465511377810583924161034503369833841).isSome = true := by
  decide +kernel

theorem k2020_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).1
      18241801894705865991896467159317630643148639773658790013893511959836934724475877140596367181593033823601).isSome = true := by
  decide +kernel

theorem k2020_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2020) 3).2 2).2 3).2
      18203681551502720499700923114789480319185340055338052859228984253578319095158473285794856889895210108273).isSome = true := by
  decide +kernel

theorem k2021_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).1 3).1
      290259064644449822114535229316989611314159886613080342497321836281973127585504574006290025288648050186097).isSome = true := by
  decide +kernel

theorem k2021_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).1 3).2
      15712825837044479289724741037162711588463132356151110380116971689856136563221994560689).isSome = true := by
  decide +kernel

theorem k2021_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).2 1).1
      4537194422539835304559952102066015911520695444980534316284291684361651958383542766225726721311874241907).isSome = true := by
  decide +kernel

theorem k2021_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).1 2).2 1).2
      62975286425164708310002811168021808104810242109402584970713802505460781713777074096700).isSome = true := by
  decide +kernel

theorem k2021_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).1 3).1
      3923510241502650378576803567273830674576181231963476524844940187918233810468561033009).isSome = true := by
  decide +kernel

theorem k2021_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).1 3).2
      980054523322174751777161891885807351345598380614020796799924618982333458843961228348).isSome = true := by
  decide +kernel

theorem k2021_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).2 1).1
      981407997605304036000458519528730831279937537866790272730475516202669430656475167916).isSome = true := by
  decide +kernel

theorem k2021_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2021) 3).2 2).2 1).2
      981425028088710808457750422474486193961346770951886452703472989481684326355052624956).isSome = true := by
  decide +kernel

theorem k2022_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2022) 3).1 2).1
      5583501980149407826949069761950427287129151347261203411443292966347072187630780884530700272091845480381188804045244906009015808243).isSome = true := by
  decide +kernel

theorem k2022_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2022) 3).1 2).2
      349349241587769288820166667451409785716485864341152204551527798412857782689451563562735160695229619467436890884502466135477530417).isSome = true := by
  decide +kernel

theorem k2022_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2022) 3).2 2).1
      5447373076815254164436213252915930612576635065856184241412933784701500424792192338320597504491843346969493115477909879562558257).isSome = true := by
  decide +kernel

theorem k2022_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2022) 3).2 2).2
      5450564788106526988596039113079171834455520578103465118796720406235690977415043409471727354302089624129154232256723177267649329).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2020 2023 :=
  (Cover.one (box := dirCellBox) (n := 2020)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2020_0) (.leaf _ k2020_1)) (.leaf _ k2020_2)) (.split 2 (.split 3 (.leaf _ k2020_3) (.leaf _ k2020_4)) (.split 3 (.leaf _ k2020_5) (.leaf _ k2020_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2021)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2021_0) (.leaf _ k2021_1)) (.split 1 (.leaf _ k2021_2) (.leaf _ k2021_3))) (.split 2 (.split 3 (.leaf _ k2021_4) (.leaf _ k2021_5)) (.split 1 (.leaf _ k2021_6) (.leaf _ k2021_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2022)
      (.split 3 (.split 2 (.leaf _ k2022_0) (.leaf _ k2022_1)) (.split 2 (.leaf _ k2022_2) (.leaf _ k2022_3))))

end C4.Cert.Dir025
