module

public import Formalism.AdmissibleDesigns.LengthSemilinear
public import Formalism.AdmissibleDesigns.FinDimOfLat
public import Formalism.AdmissibleDesigns.EKSymmCont
public import Formalism.AdmissibleDesigns.CohomZeroEquivContinuous
public import Formalism.AdmissibleDesigns.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.AdmissibleDesigns.YtTarget

@[expose] public section

-- bundled from Formalism.AdmissibleDesigns.LenComapSurj
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module

section Len

theorem len_comap_surj {O A B : Type} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    (f : A →ₗ[O] B) (hf : Function.Surjective f) (Q P : Submodule O B) :
    Module.length O (↥(Q.comap f) ⧸ (P.comap f).comap (Q.comap f).subtype) =
      Module.length O (↥Q ⧸ P.comap Q.subtype) := by
  let q : ↥(Q.comap f) →ₗ[O] ↥Q ⧸ P.comap Q.subtype :=
    (P.comap Q.subtype).mkQ ∘ₗ LinearMap.codRestrict Q (f ∘ₗ (Q.comap f).subtype) (fun x => x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨⟨a, hb⟩, rfl⟩
  have hk : LinearMap.ker q = (P.comap f).comap (Q.comap f).subtype := by
    ext x
    rw [LinearMap.mem_ker]
    exact Submodule.Quotient.mk_eq_zero _
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)] [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
  (Ψ : M →ₛₗ[(e : R →+* S)] N) (hinj : Function.Injective Ψ)
  (Q P : Submodule R M) (Q' P' : Submodule S N)
  (hQ : ∀ y, y ∈ Q' ↔ ∃ x : M, x ∈ Q ∧ Ψ x = y) (hP : ∀ x ∈ Q, x ∈ P ↔ Ψ x ∈ P')

def resQ : ↥Q →ₛₗ[(e : R →+* S)] ↥Q' where
  toFun x := ⟨Ψ (x : M), (hQ _).2 ⟨x, x.2, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add Ψ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Ψ.map_smulₛₗ c (a : M))

include hinj in
theorem resQ_bij : Function.Bijective (resQ e Ψ Q Q' hQ) := by
  constructor
  · intro a b h
    have h' : Ψ (a : M) = Ψ (b : M) := congrArg Subtype.val h
    exact Subtype.ext (hinj h')
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hQ y).1 hy
    exact ⟨⟨x, hx⟩, rfl⟩


include hinj hQ in
def resQE : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q' :=
  LinearEquiv.ofBijective (resQ e Ψ Q Q' hQ) (resQ_bij e Ψ hinj Q Q' hQ)

include hinj hQ in
theorem resQE_apply (x : ↥Q) : ((resQE e Ψ hinj Q Q' hQ x : ↥Q') : N) = Ψ (x : M) := rfl


include hinj hQ hP in
theorem len_semi :
    Module.length R (↥Q ⧸ P.comap Q.subtype) = Module.length S (↥Q' ⧸ P'.comap Q'.subtype) := by
  obtain ⟨E, hE⟩ : ∃ E : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q', ∀ x, ((E x : ↥Q') : N) = Ψ (x : M) :=
    ⟨resQE e Ψ hinj Q Q' hQ, resQE_apply e Ψ hinj Q Q' hQ⟩
  have hmap : (P.comap Q.subtype).map (E : ↥Q →ₛₗ[(e : R →+* S)] ↥Q') = P'.comap Q'.subtype := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hE]
      exact (hP x x.2).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hE] at hy
      exact ⟨x, (hP x x.2).2 hy, rfl⟩
  let F := Submodule.Quotient.equiv (P.comap Q.subtype) (P'.comap Q'.subtype) E hmap
  have h1 := Order.height_orderIso (Submodule.orderIsoMapComap F) ⊤
  rw [OrderIso.map_top] at h1
  rw [Module.length_eq_height, Module.length_eq_height]
  exact h1.symm

end Len

section Props

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))

def imRow (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  (Hf₁ i dc ρ₁ w).map (gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π (vD w) (hpD w) (heD w))

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def rowLenD (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (↥(Fs i dc VT VT' Dat w) ⧸
    (imRow i dc VT VT' Dat ρ₁ π vD hpD heD w).comap (Fs i dc VT VT' Dat w).subtype)

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  change _ = Br.toLLK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a)
  rw [Br.toLLK, IsFractionRing.lift_algebraMap]
  rfl

def RowSub (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsSubOfSums (repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x)))

def RowOrb : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) g x

def RowMat (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsMatLat (ρ := repL (eK (D.nbr i _ hn)) (Dat n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO (Dat n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ πx)))

def RowTop : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    (∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (c (Br.iota D.nbr i _ hn g))) → Continuous c) ∧
    (∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c)

def RowFin : Prop :=
  Module.Finite (D.nd.O i) T₁ ∧ Module.Free (D.nd.O i) T₁ ∧
  ∀ n ∈ K.rowsN i dc, Module.Finite (D.nd.O i) (Dat n).T' ∧ Module.Free (D.nd.O i) (Dat n).T' ∧
    ∀ v : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ t : (Dat n).T', (t : VT' n) = c • v

end Props

end Formalism.MainNotions.N.KRow

end
end

-- bundled from Formalism.AdmissibleDesigns.LocCont
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i)

theorem wpO_cont (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous (WpO D.nd i ρ π) := by
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      simp [chiU, map_inv]
    rw [he]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g
  exact hχ.smul hρ

theorem loc_cont {k : ℕ} {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous ⇑(Br.loc D.nbr i w hw M) := by
  unfold Br.loc Br.locM Br.locO mapM
  simp only [MonoidHom.coe_comp]
  refine Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)
  · first
      | exact continuous_id.matrix_map continuous_subtype_val
      | exact continuous_id.matrix_map continuous_induced_dom
  · exact continuous_id.matrix_map (D.nbr i w hw).eO_cont
  · exact continuous_subtype_val
  · first
      | exact (D.nbr i w hw).e_symm_cont
      | exact continuous_subtype_val.comp (D.nbr i w hw).e_symm_cont

theorem contW_of (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l := by
  intro v
  have hL := loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)
  have h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v :=
    hL.matrix_mulVec continuous_const
  refine h2.congr fun g => ?_
  first
    | rfl
    | simp [KDim.repW, matRep, Matrix.toLinAlgEquiv'_apply]

end Formalism.MainNotions.N.KOrb

end
end

-- bundled from Formalism.AdmissibleDesigns.LocRepTriv
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2

end Rec

end Formalism.MainNotions.N.KUnr
end
end

-- bundled from Formalism.AdmissibleDesigns.MsContW
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msContW (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : K.TBa.MsContW (i := i) (r := r) hw :=
  fun x => locC_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) x

end Formalism.MainNotions.N.KOrb

end
end

-- bundled from Formalism.AdmissibleDesigns.RowTrivialBoundOfAdmitted
section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Qcore (c : Fin (D.R.t + 1)) (n cB : ℕ) : Type :=
  ↥(Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
    (Fc i dc Dd c n).comap (Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype

def TBLenAt (cB : ℕ) (n : ℕ) (c : Fin (D.R.t + 1)) : Prop :=
  Module.length (D.nd.O i) (Qcore i dc Dd c n cB) ≤
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) * (cB : ℕ∞) *
      ((Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n) : ℕ∞) + 1)

def TBLen (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → TBLenAt i dc Dd cB n c

def TrivialBoundAtRows (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB

theorem eW_symm_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous (eW i dc hw).symm := by
  have h1 : Continuous (D.nbr i w hw).e.symm := (D.nbr i w hw).e_symm_cont
  have h2 : Continuous (MulEquiv.subgroupCongr (Dw_idx i dc hw)).symm :=
    continuous_induced_rng.2 continuous_subtype_val
  exact h2.comp h1

theorem eW_inert {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (g : Dw i dc (idx i dc w)) (hg : g ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) :
    eW i dc hw g ∈ Br.inert D.nbr i w hw := by
  have hmem : w ∈ plSet i dc := by
    simp only [plSet, Finset.mem_union]
    exact Or.inl ((dc.cover w).2 hw)
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc hmem]
  unfold Br.inert
  rw [Subgroup.mem_subgroupOf, hA] at hg
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Br.iota]
  have hx : ((Br.ι (D.nbr i w hw) (eW i dc hw g)) : GE D.nd) = (g : GE D.nd) := by
    simp [Br.ι, eW]
  rw [hx]
  exact hg


set_option maxHeartbeats 1000000 in
theorem tbTarget_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hd : TBDict i dc r π Dd)
    (hlen : TBLen i dc Dd cB) : TBTarget i dc Dd cB := by
  intro n hn c hc
  have hlen' := hlen n hn c hc
  obtain ⟨w, hwrow, rfl⟩ := Finset.mem_image.1 hn
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  obtain ⟨Y, Cd, hY, hψ, hloc⟩ := hd w hw hwrow c hc
  have hT : Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine ⟨?_, le_rfl, ?_, hlen'⟩
  · unfold Fc Hc
    split_ifs
    · exact inf_le_left
    · exact bot_le
  · intro ψ hψe z hz
    unfold Fc
    split_ifs with h1
    · obtain ⟨hzl, m, hm⟩ := tb_zero (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp
        ((Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) (eW_inert i dc hw)
        ψ hψe z hz
      rw [← map_smul]
      exact ⟨mem_locally_constant_of _ _ (hzl.comp (fun m => ((D.nd.l i : D.nd.O i) ^ cB) • m)),
        mem_unramified_of_coboundary _ _ _ m hm⟩
    · have := tb_pos (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp ψ hψe z hz
      rw [Submodule.mem_bot, ← map_smul]
      exact mkQ_eq_zero_of _ _ this

end Record

end Formalism.MainNotions.N.K.TB

end
end

