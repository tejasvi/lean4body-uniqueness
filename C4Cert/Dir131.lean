module

public import C4Check

public section

/-! Cells `4039 ≤ n < 4065` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir131

theorem k4039_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).1 3).1 1).1
      4612645050381151425987124811663478960058731055815593468496718285181626170622517756035921791608322556162620).isSome = true := by
  decide +kernel

theorem k4039_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).1 3).1 1).2
      250025906710961007947801424632314744599616907577539091886056890635121956919394176692914).isSome = true := by
  decide +kernel

theorem k4039_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).1 3).2 1).1
      975813250877512233442312478739594831239246385360390726006428963667651594645825517116).isSome = true := by
  decide +kernel

theorem k4039_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).1 3).2 1).2
      243922528080763711360292261698240022062036304805886425765918204929847074605535690156).isSome = true := by
  decide +kernel

theorem k4039_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).2 3).1 1).1
      62539062308545849018952593950050338721409980745198915225758330705383479965630177590332).isSome = true := by
  decide +kernel

theorem k4039_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).2 3).1 1).2
      62532776071823544387422841625955289904920247031620735954477116168253713094541339155634).isSome = true := by
  decide +kernel

theorem k4039_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).2 3).2 1).1
      211659255621111691514239847230333585267774390490053321587242234428).isSome = true := by
  decide +kernel

theorem k4039_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4039) 2).2 3).2 1).2
      52909534593001505501958784199044447801575100690512096447020003900).isSome = true := by
  decide +kernel

theorem k4040_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4040) 2).1 3).1 1).1
      975008744629300877001646401339634009089453690930775063388826251574465281899335382588).isSome = true := by
  decide +kernel

theorem k4040_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4040) 2).1 3).1 1).2
      60932460786620454331530510506126324693857816747737507444468403162245498279067745708).isSome = true := by
  decide +kernel

theorem k4040_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4040) 2).1 3).2
      86913124613139515774491196967349276189768889000630258312236285646646616062890446377165631457153059155162772767961753528328247537).isSome = true := by
  decide +kernel

theorem k4040_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4040) 2).2 3).1 1).1
      52868781981173176909716353267831748792996377747300149335012274748).isSome = true := by
  decide +kernel

theorem k4040_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4040) 2).2 3).1 1).2
      52864293215916960306586157231267042387317315255231919949896610364).isSome = true := by
  decide +kernel

theorem k4040_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4040) 2).2 3).2
      1603741687844438082268870289139453793767881382296717277624143368692399657116662406603164473559296274898646484264684837089305883199260444674140133948).isSome = true := by
  decide +kernel

theorem k4041_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4041) 2).1 3).1
      294321739121478655587641490616434588937004674498768506314501686135698921624682366046327594592453814546716913).isSome = true := by
  decide +kernel

theorem k4041_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4041) 2).1 3).2
      1149292428308252903976261035195054084281989196098160713586214263826808126253195680483264662187087283313468).isSome = true := by
  decide +kernel

theorem k4041_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4041) 2).2 3).1
      86889181266038638513871455466476405106375570578152472098445020145813457191105554328490982919200905125945373925445503126938628924).isSome = true := by
  decide +kernel

theorem k4041_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4041) 2).2 3).2
      18391529737747983521948588664596640296756216024332395193402447360554641850804054670877180669268663907765052).isSome = true := by
  decide +kernel

theorem k4042_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4042) 2).1 3).1
      1148885618363313996527022853500252303051043209523022159092561512221875632455497784219791574581923800898748).isSome = true := by
  decide +kernel

theorem k4042_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4042) 2).1 3).2
      1148554464011202324105880573607678376950785484255845382421375961613921371221307376731838184600632997928124).isSome = true := by
  decide +kernel

theorem k4042_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4042) 2).2 3).1
      249150451009495449062991795560167562407550558418872069130903771610264800021055503412028).isSome = true := by
  decide +kernel

theorem k4042_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4042) 2).2 3).2
      287174886931762273502712818665602634095063946228167716121124938015046004619576168697808718859385641097020).isSome = true := by
  decide +kernel

theorem k4043_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4043) 2).1
      25003181833313115866740474673187883965002928983955975488259884562386860542951804661321070272425963076804316941834571622798234848300963582804611827).isSome = true := by
  decide +kernel

theorem k4043_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4043) 2).2 3).1
      287098917348848241851979678735746952718850518475379235772827880940460738299939771013795122617213620049724).isSome = true := by
  decide +kernel

theorem k4043_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4043) 2).2 3).2
      60782081549451681993786564057545374502361253908041371120324152487077805601532008252).isSome = true := by
  decide +kernel

theorem k4044_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4044) 2).1
      1323197482857139782396947464505531524087664673870130985541680350643925157328246695994836897987198065784446479627881328768499).isSome = true := by
  decide +kernel

theorem k4044_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4044) 2).2
      338749908590354468602142188716099269248292256587563564090064347461796451762704598033631254856128111318458783534965893547259123).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4045 4046 [
    1843981174424299085014892704339995420532190020415089047905395550482381364713172695521268029457287465377671464927993975262954190072144654968888737418380896989498885574] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4046 4062 [
    17926118663592529431390679340118522621993048273097836711363305559776380090115066919379281095499597314418,
    11153685328776097516753396448153037210344454, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4062 4063 [
    5640903205868558726056799662400672882167751985163598069818769338400214185439687571278219540665035033137449787649884548512832691] = true := by
  decide +kernel

theorem k4063_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).1 2).1
      6607684893152365135297422283645257303209193297932303390249721759598488448226399488552741630346371658909468850589262813234592293901695602865579115975).isSome = true := by
  decide +kernel

theorem k4063_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).1 2).2
      295751531030199140125934901290524303719648111447748540993368875558879358188381258506934973695463352789063).isSome = true := by
  decide +kernel

theorem k4063_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4063) 3).2 2).1 2).1
      63789570526639032073257017186206740842171156914701714835602136260550195606694390226481).isSome = true := by
  decide +kernel

theorem k4063_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4063) 3).2 2).1 2).2
      864564968404352155294469287365270668564558463707006761822979675953).isSome = true := by
  decide +kernel

theorem k4063_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).2 2).2
      19279977297285083803063655211208716299627500819195765579434556828071443492617293574259334916356736114346235085).isSome = true := by
  decide +kernel

theorem k4064_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).1 3).1 2).1
      4063302337852767729796646783569513569243733387190812279568162461108507662330567028230961).isSome = true := by
  decide +kernel

theorem k4064_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).1 3).1 2).2
      4067815956103024356565331996572099534942849081479195758982788761496232833413211901774641).isSome = true := by
  decide +kernel

theorem k4064_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).1 3).2 1).1
      1195768329980542581502266620765813659611208125152081780365030741600734999795029148319181613958485667548099378).isSome = true := by
  decide +kernel

theorem k4064_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).1 3).2 1).2
      1011552607648662670451246963993891165159670488771194739837583863661654577189629109302066).isSome = true := by
  decide +kernel

theorem k4064_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).2 3).1 1).1
      15883947309056686129284615492051873954148778262042102828189378461621552902636594290226).isSome = true := by
  decide +kernel

theorem k4064_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).2 3).1 1).2
      860727087593274736826965533984821024521766121181557758784505142834).isSome = true := by
  decide +kernel

theorem k4064_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).2 3).2 1).1
      63259296948613039381457221090868792583281571811234142701866058161284024905090929081036).isSome = true := by
  decide +kernel

theorem k4064_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4064) 2).2 3).2 1).2
      1012839913695350770516430130093650843746545263570243153141229961698350379294598091338546).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4039 4065 :=
  (Cover.one (box := dirCellBox) (n := 4039)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4039_0) (.leaf _ k4039_1)) (.split 1 (.leaf _ k4039_2) (.leaf _ k4039_3))) (.split 3 (.split 1 (.leaf _ k4039_4) (.leaf _ k4039_5)) (.split 1 (.leaf _ k4039_6) (.leaf _ k4039_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4040)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4040_0) (.leaf _ k4040_1)) (.leaf _ k4040_2)) (.split 3 (.split 1 (.leaf _ k4040_3) (.leaf _ k4040_4)) (.leaf _ k4040_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4041)
      (.split 2 (.split 3 (.leaf _ k4041_0) (.leaf _ k4041_1)) (.split 3 (.leaf _ k4041_2) (.leaf _ k4041_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4042)
      (.split 2 (.split 3 (.leaf _ k4042_0) (.leaf _ k4042_1)) (.split 3 (.leaf _ k4042_2) (.leaf _ k4042_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4043)
      (.split 2 (.leaf _ k4043_0) (.split 3 (.leaf _ k4043_1) (.leaf _ k4043_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4044)
      (.split 2 (.leaf _ k4044_0) (.leaf _ k4044_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 4063)
      (.split 3 (.split 2 (.leaf _ k4063_0) (.leaf _ k4063_1)) (.split 2 (.split 2 (.leaf _ k4063_2) (.leaf _ k4063_3)) (.leaf _ k4063_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4064)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4064_0) (.leaf _ k4064_1)) (.split 1 (.leaf _ k4064_2) (.leaf _ k4064_3))) (.split 3 (.split 1 (.leaf _ k4064_4) (.leaf _ k4064_5)) (.split 1 (.leaf _ k4064_6) (.leaf _ k4064_7)))))

end C4.Cert.Dir131
