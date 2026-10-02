module

public import C4Check

public section

/-! Cells `4149 ≤ n < 4178` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir142

theorem k4149_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4149) 3).1
      3945018287388242098683912412670794081830536079539888891341345537267039969498505254706).isSome = true := by
  decide +kernel

theorem k4149_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4149) 3).2
      1161645415386084055643561795514696813856324244568669299245114836355254296089972094659182356930420394260274).isSome = true := by
  decide +kernel

theorem k4150_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4150) 2).1
      251159601467027941860337295705109082275713062894948223429008667129755174302110298420172).isSome = true := by
  decide +kernel

theorem k4150_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4150) 2).2
      62792759968196079581979599752879062430255633677069894620360920290928100088628362814412).isSome = true := by
  decide +kernel

theorem k4151_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4151) 2).1
      15653142838319956500239972318178366313471373635432406536115722485787713271156073546700).isSome = true := by
  decide +kernel

theorem k4151_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4151) 2).2
      15654574477238396822582567699805268289511710838672551801623362958416727690546031084492).isSome = true := by
  decide +kernel

theorem k4152_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4152) 2).1
      62484484083677272447375124298648697077819944643930495749244929782828592048339708486604).isSome = true := by
  decide +kernel

theorem k4152_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4152) 2).2
      15623221858506289023211213581107526680746462446265159536239241225981095659902034494412).isSome = true := by
  decide +kernel

theorem k4153_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4153) 2).1
      15973448727392666686728263033450824003996778429825084617347794268789731834899486670535740).isSome = true := by
  decide +kernel

theorem k4153_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4153) 2).2
      216494837736433982255649119874739975126250582047942866116802291842108).isSome = true := by
  decide +kernel

theorem k4154_0 : (checkBoxH dirMode depth (dirCellBox 4154)
      7750093159674131934135882321382402172050758826350248798173941866736904360335298724591546513740663006462924023123614537303087685117161048734039050376985184241518880547093564).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4155 4156 [
    1204777633018621737093997954660431836035701158208112366116463523239308910372016211739024202670027822180185619516] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4156 4157 [
    1175897124336472905352188434682305539071552404143687002951354296354938744892418299576478741152375829978741820] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4157 4158 [
    75227089078808027479500615008786891355054895203573803568497176619696356942396125127971336755989347206826017596] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4158 4159 [
    863287722490235818679639279076171199937619705674236331891058715640636] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4159 4160 [
    15548178148915133736741793319303856131424877022048941760398523314760759433277931504444] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4160 4161 [
    62181082235582500084504548449503170763149170334069964723357501846338211992810479887164] = true := by
  decide +kernel

theorem c12 : allCells dirCell 4161 4176 [
    205714078652554474698389568386328512796525117927907425658887484,
    43556700742260778461248710134493561466204, 147561929189427280484, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0] = true := by
  decide +kernel

theorem c13 : allCells dirCell 4176 4177 [
    63271577944459410875412734357109847566605163744990117764198457991602349282094752832587] = true := by
  decide +kernel

theorem c14 : allCells dirCell 4177 4178 [
    351035743038119507294626155665785088838947396201543545928501177500012634514212526818461793319905092473451143912188664576395140299] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4149 4178 :=
  (Cover.one (box := dirCellBox) (n := 4149)
      (.split 3 (.leaf _ k4149_0) (.leaf _ k4149_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4150)
      (.split 2 (.leaf _ k4150_0) (.leaf _ k4150_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4151)
      (.split 2 (.leaf _ k4151_0) (.leaf _ k4151_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4152)
      (.split 2 (.leaf _ k4152_0) (.leaf _ k4152_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4153)
      (.split 2 (.leaf _ k4153_0) (.leaf _ k4153_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4154)
      (.leaf _ k4154_0)).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14)

end C4.Cert.Dir142
