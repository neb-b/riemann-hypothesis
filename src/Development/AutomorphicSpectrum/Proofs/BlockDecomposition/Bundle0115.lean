module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepBasic
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtEdge

theorem repBasic : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic := by
  intro hExt hNat hIn
  unfold CrystallineSemistableComparison.E.InSch at hIn
  unfold CrystallineSemistableComparison.E.RepBasic
  intro R _ I X n
  unfold CrystallineSemistableComparison.E.Rep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩ m
    by_cases hm : n + 1 = m
    · exact ((hIn R X I (n - 1) n m (by omega) hm).2 α).1
    · rw [HomologicalComplex.shape I n m (by simpa using hm)]
      simp [GlobalTheory.EtC.Sec.map]
  · rintro x y a b ⟨α, rfl, rfl⟩ ⟨β, rfl, rfl⟩
    have hs := (hExt R (sch.obj X) I n α β).2 0 n (by simp) X (𝟙 X : X ⟶ X)
    exact ⟨⟨α + β, rfl, hs.1⟩, ⟨α - β, rfl, hs.2.1⟩⟩
  · rintro a ⟨α, h0, rfl⟩ k hk
    exact ((hIn R X I k n (n + 1) hk rfl).2 α).2.1 h0
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨GlobalTheory.EtC.zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h2 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) Y).2 (sch.obj Y) (sch.map f)
      (𝟙 Y : Y ⟶ Y)
    have h1 := (hNat R (sch.obj X) I n (α : Cochain _ I n) 0 n (by simp) X).1 Y f (𝟙 X : X ⟶ X)
    have e : (Sx.map (sch.map f) (𝟙 Y : Y ⟶ Y) : Sx (sch.obj X) 0 Y) = Sx.res f (𝟙 X : X ⟶ X) := by
      show 𝟙 Y ≫ f = f ≫ 𝟙 X
      simp
    refine h2.trans ?_
    rw [e]
    exact h1

end GlobalTheory.CompanionTheory.EtEdge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepConcOfInputs
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem repConc_of_inputs : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc := by
  intro hEv hSch hRep R _ I X n a
  have hS := hSch R X I (n - 1) n (n + 1) (by ring) rfl
  have hR := hRep R I X n
  have hconc : Sec.map (I.d n (n + 1)) a = 0 →
      ∃ α : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.IsConc α.1 a := by
    intro ha
    obtain ⟨α, h0, h1⟩ := hS.1 a ha
    refine ⟨α, ?_⟩
    unfold CrystallineSemistableComparison.E.IsConc
    exact ⟨h0, h1⟩
  have huniq : ∀ x y : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.Rep x a → CrystallineSemistableComparison.E.Rep y a → x = y := by
    intro x y hx hy
    have hxy : CrystallineSemistableComparison.E.Rep (x - y) (a - a) := (hR.2.2.1 x y a a hx hy).2
    rw [sub_self] at hxy
    obtain ⟨γ, hγ, hγa⟩ := hxy
    have h00 : CrystallineSemistableComparison.E.Rep (0 : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n) 0 := by
      have h := (hR.2.2.1 x x a a hx hx).2
      rwa [sub_self, sub_self] at h
    obtain ⟨b, hb⟩ := hR.2.2.2.1 0 h00 (n - 1) (by ring)
    have hγ0 : CochainComplex.HomComplex.CohomologyClass.mk γ = 0 := ((hS.2 γ).2).2 ⟨b, by rw [hb, hγa]⟩
    rw [← sub_eq_zero, ← hγ, hγ0]
  refine ⟨hconc, fun x hx => ?_, huniq⟩
  have hx' := hx
  obtain ⟨β, hβ, hβa⟩ := hx'
  have ha : Sec.map (I.d n (n + 1)) a = 0 := by
    have h := (hS.2 β).1
    rwa [hβa] at h
  obtain ⟨α, hα⟩ := hconc ha
  have hα' := hα
  unfold CrystallineSemistableComparison.E.IsConc at hα'
  obtain ⟨hα1, -⟩ := hα'
  have hRα : CrystallineSemistableComparison.E.Rep (CochainComplex.HomComplex.CohomologyClass.mk α) a := by
    unfold CrystallineSemistableComparison.E.Rep
    refine ⟨α, rfl, ?_⟩
    rw [hα1 X (𝟙 X)]
    simp [GlobalTheory.EtC.Sec.res]
  exact ⟨α, hα, huniq _ _ hRα hx⟩

end GlobalTheory.CompanionTheory.EdgeMap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepOp
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem repOp : CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp := by
  intro _ hConc hBasic hOp S R _ _ I J ρ X n x a hRep
  obtain ⟨α, hα, hmk⟩ := (hConc S I X n a).2.1 x hRep
  have hcl : Sec.map (J.d n (n + 1)) (ρ.app X n a) = 0 := by
    rw [ρ.comm X n (n + 1) a, (hBasic S I X n).2.1 x a hRep (n + 1), map_zero]
  obtain ⟨β, hβ⟩ := (hConc R J X n (ρ.app X n a)).1 hcl
  have himg : ρ.IsImage α.1 β.1 := by
    intro p s h U y
    cases p with
    | zero =>
      have hs : n = s := by omega
      subst hs
      rw [hβ.1 U y, hα.1 U y]
      exact ρ.nat y n a
    | succ p =>
      rw [hβ.2 p s h U y, hα.2 p s h U y, map_zero]
  refine ⟨β, ?_, ?_⟩
  · rw [← hOp S R I J ρ (sch.obj X) n α β himg, hmk]
  · rw [hβ.1 X (𝟙 X)]
    change ((J.X n).obj.map (𝟙 (op X))).hom (ρ.app X n a) = ρ.app X n a
    rw [CategoryTheory.Functor.map_id]
    rfl

end GlobalTheory.CompanionTheory.EdgeRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResGenRes
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtRoot

open CochainComplex CochainComplex.HomComplex

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (primRes g ζ) := by
  unfold twGen Sec.res ofRings.sec
  have h := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q i).obj (op U))
  have h2 : ((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      (Submodule.Quotient.mk (Finsupp.single (primRes g ζ) 1) : (Scheme.Γ ⋙ twF q i).obj (op V)) := by
    simp only [Functor.comp_map, twF, ModuleCat.hom_ofHom]
    erw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    unfold primRes
    rw [Scheme.Γ_map_op]
  exact h.symm.trans (congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V))) h2)

theorem resGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (resGen i ζ) = resGen i (primRes g ζ) := by
  unfold resGen
  rw [← twGen_res i g ζ]
  unfold Sec.res Sec.map
  exact (NatTrans.naturality_apply (resι (ZMod q) (tw q i)).hom g.op (twGen i ζ)).symm

theorem repRoot : CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.RepRoot := by
  intro hC hZ q i X ζ
  refine ⟨fun V g => ⟨twGen_res i g ζ, resGen_res i g ζ⟩, ?_⟩
  have hd : Sec.map ((res (ZMod q) (tw q i)).d 0 1) (resGen i ζ) = 0 :=
    ((hZ (ZMod q) (tw q i) X).2.1 (resGen i ζ)).mpr ⟨twGen i ζ, rfl⟩
  obtain ⟨α, hα⟩ := (hC (ZMod q) (res (ZMod q) (tw q i)) X 0 (resGen i ζ)).1 hd
  obtain ⟨β, hβ1, hβ2⟩ := GlobalTheory.EtC.pick_spec
    (P := fun c => ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res (ZMod q) (tw q i)) 0,
      CohomologyClass.mk α = c ∧
        ∀ (U : Scheme) (x : U ⟶ X), ev (R := ZMod q) (E := sch.obj X) (I := res (ZMod q) (tw q i)) (n := 0) (↑α) 0 0 (by simp) U x = Sec.res x (resGen i ζ))
    ⟨_, α, rfl, hα.1⟩
  unfold CrystallineSemistableComparison.E.Rep GlobalTheory.EtC.rootClass
  refine ⟨β, hβ1, (hβ2 X (𝟙 X)).trans ?_⟩
  unfold Sec.res
  simp

end GlobalTheory.CompanionTheory.EtRoot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResSplit
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ResSplitProof

theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun k => ModuleCat.Hom.hom k x) h

theorem resSplit : CrystallineSemistableComparison.E.ResLoc → CrystallineSemistableComparison.E.LocSplit → CrystallineSemistableComparison.E.LcCover → CrystallineSemistableComparison.E.ResSplit := by
  intro hRL hLS hLC R _ F U hU s x
  constructor
  · intro hx
    obtain ⟨ι, f, hf⟩ := hLS U hU _ (hRL R F s U x hx)
    obtain ⟨W, j, hj, -, -, hglue⟩ := hLC U ι f
    have hP : ∀ a, ∃ y, Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y = Sec.res (j a) x :=
      fun a => hf (W a) (j a) a (hj a)
    choose y hy using hP
    obtain ⟨z, hz, -⟩ := hglue R _ y
    obtain ⟨w, -, huniq⟩ := hglue R _ (fun a => Sec.res (j a) x)
    refine ⟨z, ?_⟩
    have h1 := huniq (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) z)
      (fun a => by rw [← map_res, hz a, hy a])
    have h2 := huniq x (fun a => rfl)
    exact h1.trans h2.symm
  · rintro ⟨y, rfl⟩
    have h := (GlobalTheory.EtC.res R F).d_comp_d (↑s) (↑(s + 1)) (↑(s + 1 + 1))
    calc Sec.map ((GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1)))
          (Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1))) y)
        = Sec.map ((GlobalTheory.EtC.res R F).d (↑s) (↑(s + 1)) ≫ (GlobalTheory.EtC.res R F).d (↑(s + 1)) (↑(s + 1 + 1))) y := rfl
      _ = Sec.map 0 y := by rw [h]
      _ = 0 := by first | rfl | simp [Sec.map]

end GlobalTheory.CompanionTheory.ResSplitProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecMapRes
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRes

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.map φ (Sec.res g y) = Sec.res g (Sec.map φ y) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun f => f.hom y) h

theorem resGood : CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.KapBij → CrystallineSemistableComparison.E.ResZero → CrystallineSemistableComparison.E.ResSplit → CrystallineSemistableComparison.E.ResGood := by
  intro hS hB hZ hX hgen q _ C _ P i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c c' φ x
    have h1 := (hS q i (P.U c) (P.ζ c) x).2.2 (P.U c') (P.S.map φ).unop
    rw [P.ζ_nat φ] at h1
    have h2 := sec_map_res (resι _ (tw q i)) (P.S.map φ).unop (kap i (P.ζ c) x)
    rw [h1] at h2
    exact h2
  · intro s c c' φ x
    exact sec_map_res ((GlobalTheory.EtC.res _ (tw q i)).d (s : ℤ) ((s + 1 : ℕ) : ℤ)) (P.S.map φ).unop x
  · intro c a b h
    exact (hB hgen q i (P.U c) (P.ζ c)).1 ((hZ _ (tw q i) (P.U c)).1 h)
  · intro c y
    have h := (hZ _ (tw q i) (P.U c)).2.1 y
    constructor
    · intro h0
      obtain ⟨t, ht⟩ := h.1 h0
      obtain ⟨f, hf⟩ := (hB hgen q i (P.U c) (P.ζ c)).2 t
      exact ⟨f, by rw [← ht, ← hf]; rfl⟩
    · rintro ⟨f, rfl⟩
      exact h.2 ⟨_, rfl⟩
  · intro s c
    exact hX _ (tw q i) (P.U c) (P.split c) s

end GlobalTheory.CompanionTheory.EdgeRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecPairApply
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.EdgeProduct

variable {q : ℕ} {C : Type 1} [Category.{0} C]

def secPair (P : Probe C q) (i i' : ℤ) (s t r : ℕ) (h : s + t = r) :
    Pairing ((P.res i).K s) ((P.res i').K t) ((P.res (i + i')).K r) where
  μ c := LinearMap.mk₂ ℤ
    (fun (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (s : ℤ)) (P.U c)) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (t : ℤ)) (P.U c)) =>
      (twPair q i i').mul (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) a b)
    (fun a a' b => by simp)
    (fun n a b => by simp)
    (fun a b b' => by simp)
    (fun n a b => by simp)
  nat {c c'} φ x y := ((twPair q i i').nat (P.S.map φ).unop (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y).symm

def resPair [NeZero q] (hK : KapMul) (hT : InTw) (P : Probe C q) (i i' : ℤ) :
    ResPair (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q)) where
  μ := secPair P i i'
  ι c x y := hK hT q i i' (P.U c) (P.ζ c) x y
  leib s t r h c x y := by
    have e := (twPair q i i').leibniz (P.U c) (s : ℤ) (t : ℤ) (r : ℤ) (by omega) x y
    have e2 : ((s : ℤ).negOnePow : ℤˣ) • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) =
        (-1 : ℤ) ^ s • (twPair q i i').mul (P.U c) (s : ℤ) ((t : ℤ) + 1) ((r : ℤ) + 1) (by omega) x
        (Sec.map ((GlobalTheory.EtC.res _ (tw q i')).d (t : ℤ) ((t : ℤ) + 1)) y) := by
      rw [Units.smul_def, Int.coe_negOnePow_natCast]
    rw [e2] at e
    exact e

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (a : Sec G U) :
    Sec.res g (Sec.res f a) = Sec.res (g ≫ f) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem term_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i : ℤ) (j : ℕ)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) {n : ℕ} (s : ComposableArrows C n)
    (g : Fin 1 → Fin (n + 1)) (hg : Monotone g) :
    term ((P.res i).K j) s (Y.glob i j a) g hg = Sec.res (Y.y (s.obj (Fin.last n))) a := by
  simp only [CH.term, Probe.Pts.glob, Probe.res, secF]
  show Sec.res _ (Sec.res _ a) = _
  rw [res_res]
  congr 1
  exact Y.nat _

theorem cupC_glob (P : Probe C q) {X : Scheme.{0}} (Y : P.Pts X) (i i' : ℤ) (j j' n : ℕ) (h : j + j' = n)
    (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) (b : Sec ((GlobalTheory.EtC.res _ (tw q i')).X (j' : ℤ)) X) :
    (secPair P i i' j j' n h).cupC (add_zero 0) (Y.glob i j a) (Y.glob i' j' b) =
      Y.glob (i + i') n ((twPair q i i').mul X (j : ℤ) (j' : ℤ) (n : ℤ) (by omega) a b) := by
  simp only [CH.Pairing.cupC, secPair]
  funext s
  simp only [LinearMap.mk₂_apply, term_glob]
  rw [← (twPair q i i').nat]
  rfl

theorem cast_cup {E : Spc} {n m k i j : ℤ} (h : n + m = k) (hc : n + m = k) (x : Ht q E n i) (y : Ht q E m j) :
    Ht.cast hc rfl (GlobalTheory.EtC.cup q x y) = (twPair q i j).cup E h x y := by
  subst hc
  rfl

theorem etCup : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.EdgeCup → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepCup →
    CrystallineSemistableComparison.E.KapMul → CrystallineSemistableComparison.E.EtCup := by
  intro hSpec hGood hEdge hBasic hRC hK hG hT q _ C _ P X Y i i' i'' hi j j' j'' hj x y
  subst hi
  have h : (j : ℤ) + (j' : ℤ) = (j'' : ℤ) := by omega
  rw [cast_cup h]
  obtain ⟨a, ha⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i)) X (j : ℤ)).1 x
  obtain ⟨b, hb⟩ := (hBasic (ZMod q) (GlobalTheory.EtC.res (ZMod q) (tw q i')) X (j' : ℤ)).1 y
  have hab := hRC (ZMod q) _ _ _ (twPair q i i') X _ _ _ h x y a b ha hb
  have ea := (hSpec hG q C P X Y i j x).1 a ha
  have eb := (hSpec hG q C P X Y i' j' y).1 b hb
  have e := hEdge ℤ C P.L P.L P.L (P.res i) (P.res i') (P.res (i + i')) (mulP (lcF P.S q))
    (resPair hK hT P i i') (hGood hG q C P i) (hGood hG q C P i') j j' j'' hj
    (Y.glob i j a) (Y.glob i' j' b) (Y.et i j x) (Y.et i' j' y) ea eb
  have e' := (congrArg (fun z => (P.res (i + i')).Edge z
    ((mulP (lcF P.S q)).cup hj (Y.et i j x) (Y.et i' j' y))) (cupC_glob P Y i i' j j' j'' hj a b)).mp e
  exact ((hSpec hG q C P X Y (i + i') j'' _).2 _ ⟨_, hab, e'⟩).symm

end GlobalTheory.CompanionTheory.EdgeProduct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecResMap
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapMulE

theorem sec_res_map {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  change ((φ.hom.app (op U) ≫ G.obj.map g.op).hom x) = ((F.obj.map g.op ≫ φ.hom.app (op V)).hom x)
  rw [φ.hom.naturality]

theorem res_kap (hKS : KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) {V : Scheme.{0}} (k : V ⟶ U) (a : ZMod q) (h : ∀ v : V, f (k v) = a) :
    Sec.res k (Sec.map (resι _ (tw q i)) (kap i ζ f)) =
      (ULift.up a : ULift.{1} (ZMod q)) • resGen i (primRes k ζ) := by
  obtain ⟨h1, -, -⟩ := hKS q i U ζ f
  unfold CrystallineSemistableComparison.E.IsLC at h1
  rw [sec_res_map, h1 V k a h]
  simp only [GlobalTheory.EtC.Sec.map, GlobalTheory.EtC.resGen, map_smul]

theorem kapMul_of : LcCover → RepRoot → KapSpec → KapMul := by
  intro hLC _ hKS hIn
  unfold CrystallineSemistableComparison.E.InTw at hIn
  intro q _ i j U ζ f g
  have hP := hIn q i j
  let fg : LocallyConstant U (ZMod q × ZMod q) :=
    ⟨fun x => (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩
  obtain ⟨W, jj, hc, -, -, hglue⟩ := hLC U (ZMod q × ZMod q) fg
  have hpt : ∀ (a : ZMod q × ZMod q) (v : W a), f (jj a v) = a.1 ∧ g (jj a v) = a.2 := by
    intro a v
    have := hc a v
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  obtain ⟨y, -, hy⟩ := hglue (ZMod q) ((res (ZMod q) (tw q (i + j))).X 0)
    (fun a => Sec.res (jj a) (Sec.map (resι (ZMod q) (tw q (i + j))) ((kap (i + j) ζ) (f * g))))
  refine (hy _ fun a => ?_).trans (hy _ fun a => rfl).symm
  rw [(twPair q i j).nat]
  rw [res_kap hKS i ζ f (jj a) a.1 fun v => (hpt a v).1,
    res_kap hKS j ζ g (jj a) a.2 fun v => (hpt a v).2,
    res_kap hKS (i + j) ζ (f * g) (jj a) (a.1 * a.2) fun v => by
      rw [LocallyConstant.mul_apply, (hpt a v).1, (hpt a v).2]]
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, hP (W a) (primRes (jj a) ζ), smul_smul, mul_comm]
  rfl

end GlobalTheory.CompanionTheory.KapMulE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSubsingleton
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TwZeroGen

theorem sec_subsingleton (hLc : LcCover) (V : Scheme.{0}) [IsEmpty V] {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton (Sec G V) := by
  let f : LocallyConstant V Empty :=
    ⟨isEmptyElim, fun s => by rw [Set.eq_empty_of_isEmpty (isEmptyElim ⁻¹' s)]; exact isOpen_empty⟩
  obtain ⟨W, j, -, -, -, hG⟩ := hLc V Empty f
  constructor
  intro a b
  exact (hG R G (fun e => e.elim)).unique (fun e => e.elim) (fun e => e.elim)

private theorem twGen_zero_eq_of_eq_pow {q : ℕ} {V : Scheme.{0}} (η θ : Prim q ↑(V.presheaf.obj (op ⊤)))
    (b : (ZMod q)ˣ) (h : η.1 = θ.1 ^ (b : ZMod q).val) : twGen 0 η = twGen 0 θ := by
  unfold twGen
  congr 1
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨θ, η, b, h, ?_⟩)
  rw [zpow_zero]
  rfl

theorem twZero : RootPow → LcCover → RepRoot → TwZero := by
  intro hR hL hP hIn q _ U ζ ξ
  obtain ⟨f, hf, hu⟩ := (hR q U ζ).2 ξ
  obtain ⟨W, j, hWf, -, -, hG⟩ := hL U (ZMod q) f
  have key : ∀ a, Sec.res (j a) (twGen 0 ζ) = Sec.res (j a) (twGen 0 ξ) := by
    intro a
    rw [((hP q 0 U ζ).1 (W a) (j a)).1, ((hP q 0 U ξ).1 (W a) (j a)).1]
    by_cases ha : IsUnit a
    · symm
      apply twGen_zero_eq_of_eq_pow _ _ ha.unit
      have hpw := hf (W a) (j a) a (hWf a)
      have e : (primRes (j a) ξ).1 = (CommRingCat.Hom.hom (Scheme.Hom.appTop (j a))) ξ.1 := rfl
      rw [IsUnit.unit_spec, e]
      exact hpw
    · haveI : IsEmpty (W a) := ⟨fun v => by
        have hv := hu (j a v)
        rw [hWf a v] at hv
        exact ha hv⟩
      exact (sec_subsingleton hL (W a) (tw q 0)).elim _ _
  obtain ⟨y, -, hy⟩ := hG (ZMod q) (tw q 0) (fun a => Sec.res (j a) (twGen 0 ζ))
  exact (hy _ (fun a => rfl)).trans (hy _ (fun a => (key a).symm)).symm

end GlobalTheory.CompanionTheory.TwZeroGen
end

