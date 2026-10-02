module

public import C4Check

public section

/-! Cells `4064 ≤ n < 4071` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir138

theorem k4064_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4064) 2).1 3).1
      86528098564422450082963121271916194339117429522698186835340934349647593130483224141607627413016436842592965920828910370386892).isSome = true := by
  decide +kernel

theorem k4064_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4064) 2).1 3).2
      4670021814532876041271225797103155578422508790527551343840256723366910735325650734636312840338433436890060).isSome = true := by
  decide +kernel

theorem k4064_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4064) 2).2 3).1
      993473080995264600992302458489072638913107040975768031226786477380434244595355603916).isSome = true := by
  decide +kernel

theorem k4064_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4064) 2).2 3).2
      63310625265928074403705755825754961820943792720771968878599750801529198191445645538252).isSome = true := by
  decide +kernel

theorem k4065_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4065) 2).1 3).1
      1009135634905438549988635348066084305201968072866857828417913134593813596627468015186892).isSome = true := by
  decide +kernel

theorem k4065_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4065) 2).1 3).2
      1160301113788307739086470653171555699633726106878466418430931064392614805428596926243146284376555995886540).isSome = true := by
  decide +kernel

theorem k4065_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4065) 2).2 3).1
      63096381473863074899534857188735819109547760803868182688699304667971996837632070726604).isSome = true := by
  decide +kernel

theorem k4065_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4065) 2).2 3).2
      15731575355373045785721336528346046406246181943345184437506657602357153669274151117772).isSome = true := by
  decide +kernel

theorem k4066_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4066) 2).1 3).1
      53157947633066143646003446299352241936868821410013496873693559868).isSome = true := by
  decide +kernel

theorem k4066_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4066) 2).1 3).2
      978996661273267914796805410156183008345736196885291693129433770917273703396461607996).isSome = true := by
  decide +kernel

theorem k4066_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4066) 2).2
      1397664796667819131210215344686922043336335611061335744754508037956607470170084933683614661162827691942760511899541335134604578611).isSome = true := by
  decide +kernel

theorem k4067_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4067) 2).1 3).1
      977595278466909087950300290491695423053104454242766221820440753521884442061031963708).isSome = true := by
  decide +kernel

theorem k4067_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4067) 2).1 3).2
      15623510709094517701651810002632917852180730054348408068035226696087776657411252142908).isSome = true := by
  decide +kernel

theorem k4067_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4067) 2).2 3).1
      212036242364493637530738190388200829736575888759386877690234846268).isSome = true := by
  decide +kernel

theorem k4067_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4067) 2).2 3).2
      211785385447677731417622071780640844104138093828478275291117304892).isSome = true := by
  decide +kernel

theorem k4068_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4068) 2).1 3).1
      3902246600187490400433586388035127601442714959626823057111338843313544537313956459068).isSome = true := by
  decide +kernel

theorem k4068_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4068) 2).1 3).2
      3382109319048489683296843612403736559075730643518368636012619876924).isSome = true := by
  decide +kernel

theorem k4068_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4068) 2).2
      25682846923216816726732396282217412690106573898452792592711013043818343805932393084095750845632628443694601767016357093993776561901770771236822917948).isSome = true := by
  decide +kernel

theorem k4069_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4069) 3).1
      5563171957872018093069638756611850679524685381490293429805408067367087927431794512191947789496184449943947150039706950271056835826).isSome = true := by
  decide +kernel

theorem k4069_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4069) 3).2
      294340029732527414705261571113914289318389560355725806112141059427707686411394512468365202700683120940512498).isSome = true := by
  decide +kernel

theorem k4070_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4070) 2).1
      287267341662203424418131838332644635598220847304444212773769052165942247973689398984224664654467560888124).isSome = true := by
  decide +kernel

theorem k4070_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4070) 2).2
      62297008093579432011859459320564048880659582324605631102972494561761185010188526539580).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4064 4071 :=
  (Cover.one (box := dirCellBox) (n := 4064)
      (.split 2 (.split 3 (.leaf _ k4064_0) (.leaf _ k4064_1)) (.split 3 (.leaf _ k4064_2) (.leaf _ k4064_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4065)
      (.split 2 (.split 3 (.leaf _ k4065_0) (.leaf _ k4065_1)) (.split 3 (.leaf _ k4065_2) (.leaf _ k4065_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4066)
      (.split 2 (.split 3 (.leaf _ k4066_0) (.leaf _ k4066_1)) (.leaf _ k4066_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4067)
      (.split 2 (.split 3 (.leaf _ k4067_0) (.leaf _ k4067_1)) (.split 3 (.leaf _ k4067_2) (.leaf _ k4067_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4068)
      (.split 2 (.split 3 (.leaf _ k4068_0) (.leaf _ k4068_1)) (.leaf _ k4068_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4069)
      (.split 3 (.leaf _ k4069_0) (.leaf _ k4069_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4070)
      (.split 2 (.leaf _ k4070_0) (.leaf _ k4070_1)))

end C4.Cert.Dir138
