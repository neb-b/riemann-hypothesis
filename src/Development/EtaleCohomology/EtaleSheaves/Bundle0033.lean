module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0011
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.TateTwists.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0016
public import Development.EtaleCohomology.EtaleSheaves.Bundle0019

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.UnderFAOf
section
noncomputable section
open CategoryTheory Limits Cardinal

namespace LateralTheory.E.UnderFAPf

def FP (X : CommRingCat.{0}) : ObjectProperty (Under X) := fun S => S.hom.hom.FinitePresentation

def model (X : CommRingCat.{0}) (i : Σ n : ℕ, Ideal (MvPolynomial (Fin n) X)) : Under X :=
  Under.mk (CommRingCat.ofHom (algebraMap X (MvPolynomial (Fin i.1) X ⧸ i.2)))

theorem fpSmall (X : CommRingCat.{0}) : ObjectProperty.EssentiallySmall.{0} (FP X) := by
  refine ⟨⟨.ofObj (model X), inferInstance, fun S hS => ?_⟩⟩
  let _ : Algebra X S.right := S.hom.hom.toAlgebra
  have hS' : Algebra.FinitePresentation X S.right := hS
  obtain ⟨n, f, hf, -⟩ := hS'.out
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  refine ⟨_, ⟨⟨n, RingHom.ker f⟩⟩, ⟨(Under.isoMk e.toRingEquiv.toCommRingCatIso ?_).symm⟩⟩
  ext x
  exact e.commutes x

attribute [local instance] fact_isRegular_aleph0

theorem fp_le (X : CommRingCat.{0}) : FP X ≤ isCardinalPresentable (Under X) (ℵ₀ : Cardinal.{0}) := by
  intro S hS
  have h := CommRingCat.isFinitelyPresentable_under X S hS
  exact h

def FPColim : Prop := ∀ (X : CommRingCat.{0}) (S : Under X),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J), (FP X).colimitsOfShape J S

theorem UnderFA_of (hC : FPColim) : LateralTheory.E.IECompPf.UnderFA := by
  intro X
  have := fpSmall X
  have hg : (FP X).IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{0}) :=
    { le_isCardinalPresentable := fp_le X
      exists_colimitsOfShape := fun S => by
        obtain ⟨J, _, _, h⟩ := hC X S
        refine ⟨J, inferInstance, ?_, h⟩
        rw [isCardinalFiltered_aleph0_iff]; infer_instance }
  exact { toHasCardinalFilteredGenerator := hg.hasCardinalFilteredGenerator }

end LateralTheory.E.UnderFAPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.WeightBoundsExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib LateralTheory.E.LeafHtpyAWPf

namespace LateralTheory.E.FreeSheafGeneratorLifts
section Lift
variable {R : Type} [CommRing R]

def freeLiftP (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift (P.obj U) => f U.unop x.down)
  naturality {U V} g := by
    refine ModuleCat.free_hom_ext fun x => ?_
    obtain ⟨x⟩ := x
    have h1 : (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      exact Finsupp.mapDomain_single
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk _)) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk _))
    rw [h1]
    erw [ ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (hf g.unop x).symm

def freeLift (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (free R).obj P ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property⟩

theorem freeLift_gen (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((freeLift P G f hf).hom.app (op U)).hom (freeGen R P U x) = f U x := by
  have := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property)
  exact this.trans (ModuleCat.freeDesc_apply (R := ULift.{1} R) _ _)

theorem freeGen_nat (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res (F := (free R).obj P) g (freeGen R P U x) := by
  have h1 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map g.op x)) := by
    simp [freeP, ModuleCat.freeMk, ModuleCat.free]
    exact Finsupp.mapDomain_single
  have h2 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  unfold freeGen
  erw [← h1]
  exact h2

theorem ev_nat {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) = Sec.res g (ev α p s h U x) := by
  unfold ev
  rw [freeGen_nat]
  exact congrArg (fun φ => φ.hom (freeGen R _ U x)) (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)

theorem sub_nat {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((E.obj (op (SimplexCategory.mk N))).map g.op x) j l h =
      (E.obj (op (SimplexCategory.mk l))).map g.op (Sx.sub x j l h) :=
  NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

variable {K : Cx R} {E : Spc} {k : ℤ}
  (F : ∀ (N : ℕ) (w : ℤ), -(N : ℤ) + k = w → ∀ U : Scheme.{0}, Sx E N U → Sec (K.X w) U)
  (hF : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U),
    Sec.res g (F N w h U x) = F N w h V ((E.obj (op (SimplexCategory.mk N))).map g.op x))

def comp (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) : ((chains R).obj E).X (-(N : ℤ)) ⟶ K.X w :=
  (chainsXIso R E N).hom ≫ freeLift _ (K.X w) (F N w h) (fun g x => hF N w h g x)

theorem comp_cast (N N' : ℕ) (e : N' = N) (hp : -(N : ℤ) = -(N' : ℤ)) (w : ℤ) (h : -(N : ℤ) + k = w)
    (h' : -(N' : ℤ) + k = w) :
    (((chains R).obj E).XIsoOfEq hp).hom ≫ comp F hF N' w h' = comp F hF N w h := by
  subst e
  simp


include hF in
theorem exists_cochain : ∃ η : Cochain ((chains R).obj E) K k,
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w h U x = F N w h U x := by
  refine ⟨Cochain.mk fun p q hpq => if hp : p ≤ 0 then
    (((chains R).obj E).XIsoOfEq (by omega : p = -(((-p).toNat : ℕ) : ℤ))).hom ≫ comp F hF (-p).toNat q (by omega)
    else 0, fun N w h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega), comp_cast F hF N _ (by omega) _ w h, comp, Iso.inv_hom_id_assoc]
  exact freeLift_gen _ _ _ _ U x

end Lift

end LateralTheory.E.FreeSheafGeneratorLifts

open LateralTheory.E.FreeSheafGeneratorLifts in
theorem LateralTheory.E.LeafHtpyAWPf.LeafHAWExists_of : LateralTheory.E.LeafHtpyAWPf.LeafHAWExists := by
  intro R _ I J K h hnat E n m k hk α β
  refine exists_cochain (fun N w hw U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow •
    h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))) ?_
  intro N w hw V U g x
  show ((K.X w).obj.map g.op).hom _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, Units.smul_def, sub_nat, sub_nat, FreeSheafGeneratorLifts.ev_nat, FreeSheafGeneratorLifts.ev_nat, ← hnat]

namespace LateralTheory.E.FreeSheafGeneratorLifts
section
variable {R : Type} [CommRing R] {I J K : Cx R}

theorem htpy' (μ μ' : Pair I J K) (H : HFam R I J K)
    (hH : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (H U s t (w - 1) (by omega) a b) +
        H U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • H U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b))
    (U : Scheme.{0}) (s t w0 w s' t' : ℤ) (h : s + t = w) (h0 : s + t = w0 + 1)
    (hs : s + 1 = s') (ht : t + 1 = t') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w0 w) (H U s t w0 h0 a b) = μ.mul U s t w h a b - μ'.mul U s t w h a b
      - H U s' t w (by omega) (Sec.map (I.d s s') a) b - s.negOnePow • H U s t' w (by omega) a (Sec.map (J.d t t') b) := by
  obtain rfl : w0 = w - 1 := by omega
  subst hs ht
  rw [hH U s t w h a b]
  abel

theorem hmul_bd_left (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    H U s t w h (bd f p y) b = bd (fun q z => H U s t w h (f q z) b) p y :=
  bd_map (((H U s t w h).flip b).toAddMonoidHom) f p y

theorem hmul_bd_right (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    H U s t w h a (bd f p y) = bd (fun q z => H U s t w h a (f q z)) p y :=
  bd_map ((H U s t w h a).toAddMonoidHom) f p y

theorem hmul_congr (H : HFam R I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w + 1) (h' : s' + t' = w + 1) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    H U s t w h (ev α p s hs U y) (ev β q t ht U z) = H U s' t' w h' (ev α p s' hs' U y) (ev β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

def Fh (H : HFam R I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w + 1 then H U _ _ w hh (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

end

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := by
  have := ev_add (a - b) b p s h U x
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem d_cocycle {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ)
    (s s' : ℤ) (hs : -(p : ℤ) + n = s) (hs' : -(p : ℤ) + (n + 1) = s') (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s s') (ev α.1 p s hs U y) =
      -((n + 1).negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = s' then ev α.1 q s' hh U z else 0) p y) := by
  have h0 := ev_delta_bd rfl α.1 p s s' hs hs' U y
  rw [(Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2] at h0
  have hz : ev (0 : Cochain ((chains R).obj E) I (n + 1)) p s' hs' U y = 0 := by
    rw [ev_eq, Cochain.zero_v, Limits.comp_zero]; rfl
  rw [hz] at h0
  exact eq_neg_of_add_eq_zero_left h0.symm

theorem recH {G : Type*} [AddCommGroup G] (X Y P P' Q Q' : G) (ε A s B K c' c e : ℤ) (hP : P' = P) (hQ : Q' = Q)
    (h1 : K * c' = -(ε * A)) (h2 : K * (c * e) = -(ε * (s * B))) :
    ε • (X - Y - -(A • P) - s • -(B • Q)) + K • (c' • P' + c • e • Q') = ε • X - ε • Y := by
  rw [hP, hQ]
  have : K • (c' • P + c • e • Q) = (K * c') • P + (K * (c * e)) • Q := by
    simp only [smul_add, smul_smul]
  rw [this, h1, h2]
  simp only [smul_sub, smul_neg, smul_smul, neg_smul]
  abel

theorem LeafHAWBounds_proved : LeafHAWBounds := by
  intro R _ I J K μ μ' H hH E n m k hk α β γ₁ γ₂ h1 h2 c hc
  apply ev_ext
  intro N w hw U x
  rw [ev_sub', ev_delta_bd (by omega : k - 1 + 1 = k) c N (-(N : ℤ) + (k - 1)) w rfl hw U x, hc N _ rfl U x, h1 N w hw U x, h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fh H α.1 β.1 U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dite_eq_left (by omega), hc N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fh
    rw [dite_eq_left (by omega)]
  rw [bd_aw (Fh H α.1 β.1 U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, htpy' μ μ' H hH U _ _ _ w (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) (by omega) (by omega) (by omega) (by omega)]
  rw [d_cocycle α p (-((p : ℕ) : ℤ) + n) _ rfl (by omega) U, d_cocycle β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl (by omega) U]
  simp only [map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, Units.smul_def, hmul_bd_left, hmul_bd_right]
  refine recH _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-1, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨(p : ℤ) - 1, by ring⟩

theorem LeafHtpyAW_proved : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := by
  intro R _ I J K μ μ' ⟨h, hnat, hht⟩ E n m k hk α β γ γ' h₁ h₂
  obtain ⟨η, hη⟩ := LeafHAWExists_of R h hnat E hk α.1 β.1
  have hc := LeafHAWBounds_proved R μ μ' h hht E hk α β γ γ' h₁ h₂ η hη
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨k - 1, by omega, η, by rw [hc]; rfl⟩

end LateralTheory.E.FreeSheafGeneratorLifts
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineHighPf

namespace LateralTheory.E.ZCovPf
set_option linter.style.haveILetI false

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have hc : (e : R →+* S).comp e.symm.toRingHom = RingHom.id S := by ext x; simp
  have hq : p = (p.map e.symm.toRingHom).map (e : R →+* S) := by
    rw [Polynomial.map_map, hc, Polynomial.map_id]
  rw [hq, show e a = (e : R →+* S) a from rfl, Polynomial.eval_map_apply, ha, map_zero]

theorem good_of_affine {A : Type} [CommRing A] {Z W : Scheme.{0}} (hZ : AICSch Z) (j : W ⟶ Z) [IsOpenImmersion j]
    [IsAffine W] (p : Z ⟶ Spec (CommRingCat.of A)) : Good (j ≫ p) := by
  by_cases hW : IsEmpty W
  · exact Or.inl hW
  right
  obtain ⟨x⟩ : Nonempty W := not_isEmpty_iff.mp hW
  have hO : IsAffineOpen (j ''ᵁ ⊤) := (isAffineOpen_top W).image_of_isOpenImmersion j
  have hne : ((j ''ᵁ ⊤ : Z.Opens) : Set Z).Nonempty := ⟨j x, x, trivial, rfl⟩
  have hA : AIC Γ(W, ⊤) := aic_of_equiv (j.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ hO hne)
  haveI : IsIntegral Z := hZ.1
  haveI : Nonempty W := ⟨x⟩
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion j
  haveI : Nonempty (⊤ : W.Opens) := ⟨⟨x, trivial⟩⟩
  let φ : A →+* Γ(W, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop).hom
  letI : Algebra A Γ(W, ⊤) := φ.toAlgebra
  refine ⟨Γ(W, ⊤), inferInstance, inferInstance, inferInstance, hA, W.isoSpec, ?_⟩
  have hφ : CommRingCat.ofHom (algebraMap A Γ(W, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (j ≫ p).appTop := rfl
  rw [hφ, Spec.map_comp, Scheme.isoSpec_hom, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

attribute [local instance] MvPolynomial.gradedAlgebra

def D (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

theorem D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X ℤ i)) (hm := Nat.one_pos)

theorem D_inf : IsAffineOpen (D 0 ⊓ D 1) := by
  have h := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 * MvPolynomial.X 1) (f_deg := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    ((MvPolynomial.isHomogeneous_X ℤ 0).mul (MvPolynomial.isHomogeneous_X ℤ 1))) (hm := Nat.two_pos)
  rw [Proj.basicOpen_mul] at h
  exact h

theorem D_cover : D 0 ⊔ D 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ)) ?_
  · refine eq_top_iff.mpr (le_trans (le_of_eq h.symm) (iSup_le fun i => ?_))
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · intro x hx
    have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx
    have hc : AddMonoidAlgebra.coeff x 0 = 0 := by
      rw [GradedRing.proj_apply] at h0
      have e : ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) x) 0 : MvPolynomial (Fin 2) ℤ) =
          MvPolynomial.homogeneousComponent 0 x := MvPolynomial.decomposition.decompose'_apply x 0
      rw [e] at h0
      have := congrArg (AddMonoidAlgebra.coeff · 0) h0
      rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero] at this
      simpa using this
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push Not at hne
    have hm0 : m = 0 := Finsupp.ext fun i => hne i trivial
    subst hm0
    exact (MvPolynomial.mem_support_iff.mp hm) hc

theorem projectiveLine_integers_affine_cover_absolutely_integrally_closed : ZCov := by
  intro A _ Z p hp hZ
  obtain ⟨L, u, l, hu, ⟨-, f0, hpb⟩, rfl⟩ := hp
  have hf0 : IsAffineHom f0 :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) hpb.flip inferInstance
  let φ : Z ⟶ P1 := u ≫ f0
  let U : Z.Opens := φ ⁻¹ᵁ D 0
  let V : Z.Opens := φ ⁻¹ᵁ D 1
  have hU : IsAffineOpen U := (D_affine 0).preimage φ
  have hV : IsAffineOpen V := (D_affine 1).preimage φ
  have hUV : IsAffineOpen (U ⊓ V) := D_inf.preimage φ
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  haveI : IsAffine (U ⊓ V : Z.Opens) := hUV
  haveI : IsAffine (pullback U.ι V.ι) := IsAffine.of_isIso (isPullback_opens_inf U V).isoPullback.inv
  refine ⟨U, V, U.ι, V.ι, inferInstance, inferInstance, ?_, good_of_affine hZ U.ι _, good_of_affine hZ V.ι _, ?_⟩
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have h := congrArg (fun O : P1.Opens => ((φ ⁻¹ᵁ O : Z.Opens) : Set Z)) D_cover
    simpa [U, V] using h
  · rw [← Category.assoc]
    exact good_of_affine hZ (pullback.fst U.ι V.ι ≫ U.ι) _

end LateralTheory.E.ZCovPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZarIndPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.ZarIndPf

def Bij (q : ℕ) (i n : ℤ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : Prop :=
  Function.Bijective (pull _ (sch.map (fO f p U)) (tw q i) n)

def InjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)

def SurjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Surjective (pull _ (sch.map (fO f p U)) (tw q i) n)

def Step : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U

theorem Step_of (h1 : InjStep) (h2 : SurjStep) : Step := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  exact ⟨h1 hM hH q f p hq i n hg hb U hU, h2 hM hH q f p hq i n hg hb (h1 hM hH q f p hq i n hg hb) U hU⟩

theorem pull_bij_of_iso {E E' : Spc} (g : E ⟶ E') [IsIso g] {q' : ℕ} (F : Shv (ZMod q')) (n : ℤ) :
    Function.Bijective (pull _ g F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (inv g) F n, fun x => ?_, fun x => ?_⟩
  · simp [← pull_comp, pull_id]
  · simp [← pull_comp, pull_id]

theorem bij_top {q : ℕ} {i n : ℤ} {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsIso (⊤ : S.Opens).ι] (h : Bij q i n f p ⊤) :
    Function.Bijective (pull _ (sch.map f) (tw q i) n) := by
  have e : fO f p ⊤ ≫ pullback.fst p (⊤ : S.Opens).ι = pullback.fst (f ≫ p) (⊤ : S.Opens).ι ≫ f := by
    exact pullback.lift_fst _ _ _
  have e2 : ∀ x, pull _ (sch.map (fO f p ⊤)) (tw q i) n (pull _ (sch.map (pullback.fst p (⊤ : S.Opens).ι)) _ n x) =
      pull _ (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) _ n (pull _ (sch.map f) _ n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, e]
  have b1 := pull_bij_of_iso (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n
  have b2 := pull_bij_of_iso (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n
  have hc : Function.Bijective ((pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n)) := by
    have : (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n) =
        (pull (ZMod q) (sch.map (fO f p ⊤)) (tw q i) n) ∘ (pull (ZMod q) (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n) :=
      funext fun x => (e2 x).symm
    rw [this]; exact h.comp b1
  refine ⟨hc.1.of_comp, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hc.2 (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n y)
  exact ⟨x, b2.1 hx⟩

theorem bij_neg (hH : Hyp) {q : ℕ} {i n : ℤ} (hn : n < 0) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    Bij q i n f p U := by
  have h1 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO p U)) n hn
  have h2 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO (f ≫ p) U)) n hn
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem ZarInd_of_step (hS : Step) : ZarInd := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i hg
  have P : ∀ n : ℤ, ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U := by
    intro n
    induction n using Int.induction_on with
    | zero => exact hS hM hH q f p hq i 0 (fun s => hg s 0) (fun U _ => bij_neg hH (by norm_num) f p U)
    | succ m ih =>
      exact hS hM hH q f p hq i (m + 1) (fun s => hg s (m + 1)) (by simpa using ih)
    | pred m ih =>
      exact fun U _ => bij_neg hH (by omega) f p U
  intro n
  have : IsIso (⊤ : S.Opens).ι := (Scheme.topIso S).isIso_hom
  exact bij_top f p (P n ⊤ (by simpa using isCompact_univ))

end LateralTheory.E.ZarIndPf
end
end

