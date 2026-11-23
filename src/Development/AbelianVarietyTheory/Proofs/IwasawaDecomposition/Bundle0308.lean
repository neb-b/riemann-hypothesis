module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IdxMatNF
public import Formalism.LocalToGlobal.Columns.ChainTw
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassEquivReferenceTupleEqSelf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroCls

theorem stepZeroClassEquiv_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word)
    (c : (I.stp u I.mu0 0).Cl), I.eCls0 l u I.mu0 c = c := by
  intro B X I h l u c
  show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep c)) = c
  refine Eq.trans ?_ (GlobalTheory.Mem.Col2.ClsZero.cl_rep _ c)
  refine (GlobalTheory.Mem.Col2.ClsZero.cl_eq_iff h u I.mu0 _ _ _ _).2 ?_
  rfl

end GlobalTheory.Mem.Col2.TC.MuZeroCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroColumnsClassSumFormPosDef
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df


set_option maxHeartbeats 1600000 in
theorem cols_ipV_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (c : ((I.cols l).mem u).C.cls 0)
    (f g : ((I.cols l).mem u).C.Y 0 → ℂ) :
    ((I.cols l).fm u).ipV 0 c f g = starRingEnd ℂ (((I.cols l).fm u).ipV 0 c g f) :=
  ClassSumPos.ipVal_herm _ _ _ f g

theorem cols_ipC_herm {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word)
    (φ ψ : ((I.cols l).mem u).C.cls 0 → ((I.cols l).mem u).C.Y 0 → ℂ) :
    starRingEnd ℂ (((I.cols l).fm u).ipC 0 ψ φ) = ((I.cols l).fm u).ipC 0 φ ψ := by
  unfold MemberForms.ipC
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, cols_ipV_herm I l u c (φ c) (ψ c)]
  congr 1
  simp [ColumnChain.wt]

theorem cols_pos : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok),
    SpectralModel.ColsPos (I.cols l) := by
  intro B X I _ _ l _ u
  refine ⟨fun x _ y _ => cols_ipC_herm I l u x y, fun x hx h0 => ?_⟩
  exact ipC_zero_re_pos B (I.cols l) u (fun φ ψ => (cols_ipC_herm I l u ψ.1 φ.1).symm) ⟨x, hx⟩
    (fun h => h0 (congrArg Subtype.val h))

end GlobalTheory.Mem.Df
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroHermitianLevelUniformiserKillsValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LevTwist

section Re

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  have e : ((reV (rfl : a = a) E : (Fin a → E) →ₗ[E] (Fin a → E)).restrictScalars (𝓞 E)) = LinearMap.id :=
    LinearMap.ext fun x => funext fun i => rfl
  rw [reL, e, Submodule.map_id]

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  rfl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fun_transport {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E))
    (hL : Lb' = reL h Lb) (v : HeightOneSpectrum (𝓞 F)) {M : Type} [AddCommGroup M] [Module (intV E v) M]
    (f' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J' Lb')) →ₗ[intV E v] M) :
    ∃ f : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) →ₗ[intV E v] M,
      (f' ≠ 0 → f ≠ 0) ∧ (∀ r : intV E v, (∀ x, f' (r • x) = 0) → ∀ x, f (r • x) = 0) ∧
      ((∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb' → f' x = 0) →
        ∀ x, x.1 ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb → f x = 0) ∧
      ∀ (U : Subgroup (GL (Fin a) (E ⊗[F] v.adicCompletion F))) (U' : Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F))),
        U' = U.map (reGL h _).toMonoidHom → U' = levelVL σ J' v Lb' ⊓ stabFun _ f' →
        U = levelVL σ J v Lb ⊓ stabFun _ f := by
  subst h
  obtain rfl : J' = J := by
    rw [hJ]; ext i j; rfl
  obtain rfl : Lb' = Lb := by rw [hL, reL_rfl]
  refine ⟨f', id, fun _ h => h, id, ?_⟩
  rintro U U' rfl h
  rw [← h]
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · intro hg
    exact ⟨g, hg, reGL_rfl _ g⟩
  · rintro ⟨g', hg', e⟩
    have : g' = g := (reGL_rfl _ g').symm.trans e
    exact this ▸ hg'

end Re

section Pi

theorem smul_eq_zero_of_prime_card {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] {p : ℕ} (hp : p.Prime)
    (hc : Nat.card M = p) (a : S) {m₀ : M} (h1 : m₀ ≠ 0) (h2 : a • m₀ = 0) (m : M) : a • m = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc h1 (g' := m))
  rw [smul_comm, h2, smul_zero]


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem pi_kills {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi) (K : ClsTied u i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe) (v : (D.mem u).A.vT)
    (a : intV D.host.E (A.eV v).1)
    (ha : (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) =
      inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU : 𝓞 D.host.E) : D.host.E))
    (m : K.lev.fM (A.eV v).1 (A.eV v).2) : a • m = 0 := by
  obtain ⟨c, -⟩ := K.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨x, hx⟩ : ∃ x, (D.fm u).fv i v c x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact (D.fm u).fv_ne i v c (LinearMap.ext hc)
  obtain ⟨z, rfl⟩ := P.pr_surj v c x
  have hin : ∀ z : ↥(Ld D u i hi c), ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
    fun z => (GlobalTheory.LevelHecke.MovePair.ld_loc K _ c _).1 (Submodule.subset_span ⟨z.1, z.2, rfl⟩)
  have h1 : K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ ≠ 0 := by
    intro h0
    apply hx
    rw [hT v c z (hin z), h0, map_zero]
  have h3 : K.lev.fT _ (A.eV v).2 ⟨_, hin (A.piU • z)⟩ = 0 := by
    have hz0 : (D.fm u).fv i v c (P.pr v c (A.piU • z)) = 0 := by
      rw [P.pr_smul, A.res_pi, zero_smul, map_zero]
    exact (fMe v).injective (((hT v c _ (hin _)).symm.trans hz0).trans (map_zero (fMe v)).symm)
  have e : a • (⟨_, hin z⟩ : latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))) =
      ⟨_, hin (A.piU • z)⟩ := by
    apply Subtype.ext
    have e1 : (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b)) =
        (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
          fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b) := by
      funext b
      rw [ha]
      show inclE (F := D.host.F) _ (((A.piU : 𝓞 D.host.E) : D.host.E) * z.1 b) = _
      rw [map_mul]
      rfl
    show (a : D.host.E ⊗[D.host.F] (A.eV v).1.adicCompletion D.host.F) •
        (((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 b))) =
        ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
          (fun b => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) ((A.piU • z).1 b))
    rw [e1, Matrix.mulVec_smul]
  have h2 : a • K.lev.fT _ (A.eV v).2 ⟨_, hin z⟩ = 0 :=
    (map_smul (K.lev.fT _ (A.eV v).2) a _).symm.trans ((congrArg (K.lev.fT _ (A.eV v).2) e).trans h3)
  exact smul_eq_zero_of_prime_card (D.mem u).A.T_prime (K.lev.fM_card _ _) a h1 h2 m

end Pi

section Main


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem stepZeroHermitianLevel_with_formsFunctional (D : D7) (u : D.what₂.Word) {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}
    (F : FormsTiedSym D u Ch chOf)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (hS : SameCar (rank_eq_first_level D.R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U
      (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1)
      (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1)) :
    ∃ L' : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u),
      L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧
      ∀ (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal)
        (a : intV D.host.E w),
        (a : TensorProduct D.host.F D.host.E (w.adicCompletion D.host.F)) =
          inclE (F := D.host.F) (w.adicCompletion D.host.F) ((F.atT.piU : 𝓞 D.host.E) : D.host.E) →
        ∀ m : L'.fM w h, a • m = 0 := by
  have hJ : gramN D 0 (Nat.zero_le _) =
      (D.sp.gram0).reindex (finCongr (rank_eq_first_level D.R)) (finCongr (rank_eq_first_level D.R)) := by
    ext i j
    rfl
  have key := fun (w : HeightOneSpectrum (𝓞 D.host.F)) (h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ w.asIdeal) =>
    fun_transport (rank_eq_first_level D.R) (sigD D) D.sp.gram0 (gramN D 0 (Nat.zero_le _)) hJ L.Lb
      (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb hS.Lb_eq w
      ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT w h)
  choose fT' k1 k2 k3 k4 using key
  refine ⟨{ L with
    fM := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM
    fM_acg := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_acg
    fM_mod := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_mod
    fT := fT'
    fT_ne := fun v h => k1 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_ne v h)
    fT_T := fun v h => k2 v h _ ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_T v h)
    fM_card := (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fM_card
    fT_L := fun v h => k3 v h ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.fT_L v h)
    UlocAlt := fun v h => k4 v h _ _ (hS.Uloc_eq v) ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.UlocAlt v h) },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro w h a ha m
  obtain ⟨v, hv⟩ := F.atT.eV.surjective ⟨w, h⟩
  have hw : (F.atT.eV v).1 = w := congrArg Subtype.val hv
  subst hw
  exact pi_kills (F.lv 0 (Nat.zero_le _)) (F.cls 0 (Nat.zero_le _) (Or.inl rfl))
    (F.fMe 0 (Nat.zero_le _) (Or.inl rfl)) (F.fv 0 (Nat.zero_le _) (Or.inl rfl)) v a ha m

end Main


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem stepZeroHermitianLevel_uniformiser_kills_values : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 :=
  by
  intro B X I _ _ l Z u Ch chOf F _ L hS
  exact stepZeroHermitianLevel_with_formsFunctional (I.rec7 l Z) u F L hS

end GlobalTheory.Mem.Col2.LevTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem underQ_notMem {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : I.UnderQ a v) :
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  obtain ⟨P, hP, rfl⟩ := hv
  have key : ∀ p : ℕ, p.Prime → p ∈ I.S → ((p : ℕ) : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
    intro p hp hS hm
    apply GlobalTheory.KFormsCmp.notMem_of_QE hI.sel_ok (I.tup a) hP hp hS
    have := Ideal.mem_comap.1 hm
    simpa using this
  exact ⟨key _ (l.pr.T_prime u) (hI.T_mem u), fun j => key _ (l.pr.g_prime j) (hI.g_mem j)⟩

theorem underQ_prime_to_bad : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι)
    (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v →
    ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal :=
  fun I hI l u a v hv => underQ_notMem I hI l u a v hv

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedNormalForms
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.Proof.TwistedNormalForms

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.QNormal

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem sum_ite_zero_eq_atN {n c : ℕ} (y : Fin (n + c) → E) :
    ∑ i : Fin c, (if i.1 = 0 then y (Fin.natAdd n i) else 0) = Loc.atN y n := by
  cases c with
  | zero => simp [Loc.atN]
  | succ c =>
    rw [Fin.sum_univ_succ]
    have h0 : ∀ i : Fin c, ¬ ((Fin.succ i).1 = 0) := fun i => by simp
    simp only [Fin.val_zero, if_true, h0, if_false, Finset.sum_const_zero, add_zero]
    unfold Loc.atN
    rw [dite_eq_left (by omega)]
    congr 1

theorem comb_natAdd (q : ℕ) {n c : ℕ} (e : Fin c → ℤ) (z : Sp E n) (l : Sp E n) (s : Fin c → E) (b : Fin c) :
    (Loc.inX E n c l + ∑ i, s i • nfGen q n c e z i) (Fin.natAdd n b) = (q : E) ^ e b * s b := by
  have hx : ∀ w : Sp E n, Loc.inX E n c w (Fin.natAdd n b) = 0 := fun w => by
    rw [inX_apply, dite_eq_right (by simp)]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, hx, zero_add]
  rw [Finset.sum_eq_single b]
  · have : (if b.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by
      split_ifs <;> simp [hx]
    simp [Loc.eN, this]
    ring
  · intro i _ hib
    have hne : ¬ ((Fin.natAdd n b).1 = n + i.1) := by
      intro h; apply hib; ext; simp at h; omega
    have : (if i.1 = 0 then Loc.inX E n c z else 0) (Fin.natAdd n b) = 0 := by
      split_ifs <;> simp [hx]
    have hne' : ¬ (b.1 = i.1) := fun h => hib (Fin.ext h).symm
    simp [Loc.eN, hne', this]
  · simp

theorem comb_castAdd (q : ℕ) {n c : ℕ} (e : Fin c → ℤ) (z : Sp E n) (l : Sp E n) (s : Fin c → E) (a : Fin n) :
    (Loc.inX E n c l + ∑ i, s i • nfGen q n c e z i) (Fin.castAdd c a) =
      l a + (∑ i : Fin c, (if i.1 = 0 then (q : E) ^ e i * s i else 0)) * z a := by
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, nfGen, smul_eq_mul, inX_castAdd, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hne : ¬ (a.1 = n + i.1) := by omega
  split_ifs with hi
  · simp [Loc.eN, hne, inX_castAdd]; ring
  · simp [Loc.eN, hne]

end Lattice

theorem twNF_imp_matNF : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)),
    P ∉ Pr.vGs → ∀ h : AutY X R j, TwNF (Pr := Pr) j P h → GlobalTheory.QNF.MatNF Pr R j P h := by
  intro X Pr R j P hP h hT
  refine (GlobalTheory.QNF.nf_iff_matNF X Pr R j P hP h).1 ?_
  obtain ⟨n, z, hn, hz, hcrit⟩ := hT
  refine ⟨fun i => n i.1, z, fun i => hn i.1, hz, ?_⟩
  have hq := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P
  have hzV := (mem_stdAt_iff z).1 hz
  ext y
  have hmem : y ∈ h '' (lamYat (Pr := Pr) (R := R) j P : Set _) ↔ h⁻¹ y ∈ lamYat (Pr := Pr) (R := R) j P := by
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨h⁻¹ y, hy, by simp⟩
  rw [hmem, hcrit y]
  constructor
  · rintro ⟨hX, hN⟩
    refine ⟨fun a => y (Fin.castAdd _ a) - Loc.atN y (R.N j) * z a, (mem_stdAt_iff _).2 hX,
      fun i => ((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i), hN, ?_⟩
    funext p
    refine Fin.addCases (fun a => ?_) (fun b => ?_) p
    · rw [comb_castAdd]
      have : ∀ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * (((qOf P : X.E) ^ n i.1)⁻¹ * y (Fin.natAdd _ i)) else 0)
          = (if i.1 = 0 then y (Fin.natAdd _ i) else 0) := fun i => by
        rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]
      simp only [this, sum_ite_zero_eq_atN]
      ring
    · rw [comb_natAdd, mul_inv_cancel_left₀ (zpow_ne_zero _ hq)]
  · rintro ⟨l, hl, s, hs, rfl⟩
    have hlV := (mem_stdAt_iff l).1 hl
    have hb := comb_natAdd (qOf P) (fun i : Fin (cOf R j) => n i.1) z l s
    have hat : Loc.atN (Loc.inX X.E (R.N j) (cOf R j) l + ∑ i, s i • nfGen (qOf P) (R.N j) (cOf R j) (fun i => n i.1) z i) (R.N j)
        = ∑ i : Fin (cOf R j), (if i.1 = 0 then (qOf P : X.E) ^ n i.1 * s i else 0) := by
      rw [← sum_ite_zero_eq_atN]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb i]
    refine ⟨fun a => ?_, fun i => ?_⟩
    · rw [comb_castAdd, hat, add_sub_cancel_right]
      exact hlV a
    · rw [hb i, inv_mul_cancel_left₀ (zpow_ne_zero _ hq)]
      exact hs i

end GlobalTheory.Proof.TwistedNormalForms
end
end

