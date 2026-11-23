module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.SharpRestriction.GrowthBounds.DataG

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianColumns.CompletionIntegersIff
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def awayFrom₂ (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Subgroup (GL (Fin R.k) (E ⊗[F] Af F)) :=
  UPts sp.cm.sig sp.gram0 (Af F) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal), (L.Uloc v).comap (bc (prV (E := E) v))

structure GLevTie (L : ColLevel R F E sp gp C A clsLat) {p : ℕ} (G : Formalism.MainNotions.G.GAtP p) where

  rk : G.P.m + 1 = R.k

  pl : Fin G.P.nV ≃ {v : HeightOneSpectrum (𝓞 F) // ((p : ℕ) : 𝓞 F) ∈ v.asIdeal}

  eQ : ∀ (v : Fin G.P.nV) (w : HeightOneSpectrum (𝓞 F)), (pl v).1 = w → G.P.Qq v ≃+* w.adicCompletion F
  completion_integers_iff : ∀ v w (h : (pl v).1 = w) (x : G.P.Qq v),
    x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔ eQ v w h x ∈ w.adicCompletionIntegers F

  spl : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F
  spl_sig : ∀ w h x, spl w h (sigR sp.cm.sig (w.adicCompletion F) x) = swapR _ (spl w h x)

  spl_alg : ∀ w h (a : w.adicCompletion F), spl w h ((1 : E) ⊗ₜ[F] a) = (a, a)

  fr : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → GL (Fin R.k) (w.adicCompletion F)
  fr_lat : ∀ w h (t : Fin R.k → w.adicCompletion F),
    (∃ x ∈ locL w L.Lb, ∀ a, (spl w h (x a)).1 = t a) ↔
      ∀ a, (((fr w h)⁻¹ : GL (Fin R.k) (w.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (w.adicCompletion F)).mulVec t a ∈ w.adicCompletionIntegers F

  yG : G.comp → UPts sp.cm.sig sp.gram0 (Af F)
  yG_p : ∀ i (w : HeightOneSpectrum (𝓞 F)), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
    bc (prV (E := E) w) (yG i : GL (Fin R.k) (E ⊗[F] Af F)) = 1
  yG_bij : Function.Bijective (fun i : G.comp =>
    (Quotient.mk'' (yG i) : ClassSet
      ((ratPts sp.cm.sig sp.gram0 (Af F)).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F)))
      ((awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (Af F)))))

  gamI : ∀ i, (G.lev i).Γ →* UJ (sp.cm.sig : E →+* E) sp.gram0
  gamI_inj : ∀ i, Function.Injective (gamI i)
  gamI_range : ∀ i (γ : UJ (sp.cm.sig : E →+* E) sp.gram0), γ ∈ (gamI i).range ↔
    bc (inclE (F := F) (Af F)) (γ : GL (Fin R.k) E) ∈
      (awayFrom₂ L p).map (MulAut.conj (yG i : GL (Fin R.k) (E ⊗[F] Af F))).toMonoidHom

  act_eq : ∀ i v w (h : (pl v).1 = w) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (γ : (G.lev i).Γ)
    (a b : Fin (G.P.m + 1)) (a' b' : Fin R.k), (a : ℕ) = a' → (b : ℕ) = b' →
    eQ v w h (((G.lev i).act v γ : GL (Fin (G.P.m + 1)) (G.P.Qq v)) a b) =
      (((fr w hw)⁻¹ * bc ((RingHom.fst _ _).comp (spl w hw).toRingHom)
        (bc (inclE (F := F) (w.adicCompletion F)) (gamI i γ : GL (Fin R.k) E)) * fr w hw :
          GL (Fin R.k) (w.adicCompletion F)) : Matrix (Fin R.k) (Fin R.k) (w.adicCompletion F)) a' b'

theorem GLevTie.spl_F {L : ColLevel R F E sp gp C A clsLat} {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (X : GLevTie L G)
    (w : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : F) :
    (X.spl w h (inclE (F := F) (w.adicCompletion F) (algebraMap F E a))).1 = algebraMap F (w.adicCompletion F) a := by
  have : inclE (F := F) (w.adicCompletion F) (algebraMap F E a) =
      (1 : E) ⊗ₜ[F] (algebraMap F (w.adicCompletion F) a) := by
    show (algebraMap F E a) ⊗ₜ[F] (1 : w.adicCompletion F) = _
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
  rw [this, X.spl_alg]

end Formalism.L2.Herm

end
end

-- bundled from Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
section
noncomputable section

namespace Formalism.L2.Herm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def toGLb {V : Type} [AddCommGroup V] [Module E V] {n : ℕ} (b : Module.Basis (Fin n) E V) :
    (V ≃ₗ[E] V) ≃* GL (Fin n) E :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

def AdStep {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (U : Subgroup (GL (Fin n) (E ⊗[F] Af F)))
    (y y' : GL (Fin n) (E ⊗[F] Af F)) (γ : GL (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ κ ∈ U, ∃ η ∈ UPts σ J (Af F), (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → bc (prV (E := E) w) η = 1) ∧
    bc (inclE (F := F) (Af F)) γ * y' = y * η * κ

def UAd (hc : CMData F E) (S : HSpace E) : Subgroup (GL (Fin S.rank) (E ⊗[F] AdeleRing (𝓞 F) F)) :=
  UPts hc.sig S.gram (AdeleRing (𝓞 F) F)

theorem mem_dual (S : HSpace E) (L : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT L ↔ ∀ y ∈ L, S.hT y x ∈ (algebraMap (𝓞 E) E).range := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one,
    RingHom.mem_range]

theorem crdLat_dual (hc : CMData F E) (S : HSpace E) (L : Submodule (𝓞 E) S.V) :
    crdLat S (Formalism.HermitianLatticesTheory.dual S.hT L) = dualL hc S (crdLat S L) := by
  have key : ((crdLat S (Formalism.HermitianLatticesTheory.dual S.hT L) : Submodule (𝓞 E) (Fin S.rank → E)) : Set (Fin S.rank → E)) =
      dualSet (hc.sig : E →+* E) S.gram (crdLat S L) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩ s ⟨y, hy, rfl⟩
      have := (mem_dual S L x).1 hx y hy
      rw [hT_crd hc] at this
      exact this
    · intro ht
      refine ⟨(crd S).symm t, ?_, by simp⟩
      refine (mem_dual S L _).2 fun y hy => ?_
      rw [hT_crd hc]
      have := ht (crd S y) ⟨y, hy, rfl⟩
      simpa using this
  unfold dualL
  rw [← key, Submodule.span_eq]

theorem coordinate_lattice_self_dual (hc : CMData F E) (S : HSpace E) : dualL hc S (crdLat S S.L0) = crdLat S S.L0 := by
  rw [← crdLat_dual, show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]

end Formalism.L2.Herm

end
end

-- bundled from Formalism.LocalToGlobal.HermitianColumns.SplitGAlg
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

structure ColLevelX {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (inK : E → Prop) (piU : 𝓞 E)
    (e : A.vT ≃ {v : HeightOneSpectrum (𝓞 F) // ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal})
    (fz : ∀ (v : A.vT) (c : C.cls 0), Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → A.Fv v) where

  piG : Fin 2 → 𝓞 E
  piG_K : ∀ i, inK (piG i : E)
  piG_norm : ∀ i, (piG i : E) * star (piG i : E) = (gp i : E)

  splitG_pi : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal),
    Valued.v (L.splitG i v h (inclE (F := F) (v.adicCompletion F) (star (piG i : E)))).1 < 1

  splitG_alg : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (a : v.adicCompletion F),
    L.splitG i v h ((1 : E) ⊗ₜ[F] a) = (a, a)

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (t : Fin R.k → v.adicCompletion F),
    (∃ x ∈ locL v L.Lb, ∀ a, (L.splitG i v h (x a)).1 = t a) ↔
      ∀ a, (((L.frG i v h)⁻¹ : GL (Fin R.k) (v.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F

  fM_pi : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal) (a : intV E v),
    (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (piU : E) →
    ∀ m : L.fM v h, a • m = 0

  fMe : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal), L.fM w h ≃+ A.Fv (e.symm ⟨w, h⟩)

  fv0 : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal) (c : C.cls 0)
    (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c))
    (t : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
    ((bc (prV (E := E) w) (L.y c : GL (Fin R.k) (E ⊗[F] Af F)) : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] w.adicCompletion F)).mulVec t.1 =
      (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
    fz (e.symm ⟨w, h⟩) c z = fMe w h (L.fT w h t)

end Formalism.L2.Herm

end
end

-- bundled from Formalism.LocalToGlobal.HermitianColumns.StepLevelQ
section
noncomputable section

namespace Formalism.L2.Herm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure StepLevelQ (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (T f : ℕ)
    (Q : Finset (HeightOneSpectrum (𝓞 F))) where

  Lb : Submodule (𝓞 E) (Fin S.rank → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_span : Submodule.span E (Lb : Set (Fin S.rank → E)) = ⊤
  Lb_int : Lb ≤ dualL hc S Lb
  Lb_dual : ∀ y ∈ dualL hc S Lb, (T : E) • y ∈ Lb
  Lb_index : Lb.toAddSubgroup.relIndex (dualL hc S Lb).toAddSubgroup = T ^ (2 * f)

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((T : 𝓞 F) ∉ v.asIdeal) → v ∉ Q → Uloc v = levelVL hc.sig S.gram v Lb
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
    ∀ x, InPrinc hc S v (gp i) Lb x → x ∈ Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ Uloc v ↔ InLocalDiscriminantKernel hc S v Lb x
  Uloc_Q : ∀ v ∈ Q, ∃ N : ℕ, 0 < N ∧ ∀ x, InPrinc hc S v N Lb x → x ∈ Uloc v

  U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

end Formalism.L2.Herm

end
end

