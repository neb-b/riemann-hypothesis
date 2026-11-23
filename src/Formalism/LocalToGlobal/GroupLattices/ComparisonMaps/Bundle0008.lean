module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0001
public import Formalism.LocalRingCardinality.Lemmas

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsStab
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

attribute [local irreducible] Formalism.L2.G.repP

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ}

def StabU (L : ColLevel R F E sp gp C A clsLat) (x : GA sp) : Type :=
  {γ : UJ (sp.cm.sig : E →+* E) sp.gram0 // x⁻¹ * ratA sp γ * x ∈ KA L}

def TrivStabU (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  ∀ (x : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0), x⁻¹ * ratA sp γ * x ∈ KA L → γ = 1

def stabConj (x x' : GA sp) (h0 : UJ (sp.cm.sig : E →+* E) sp.gram0) (κ : GA sp) (hκ : κ ∈ KA L)
    (e : x' = ratA sp h0 * x * κ) : StabU L x ≃ StabU L x' where
  toFun γ := ⟨h0 * γ.1 * h0⁻¹, by
    have : x'⁻¹ * ratA sp (h0 * γ.1 * h0⁻¹) * x' = κ⁻¹ * (x⁻¹ * ratA sp γ.1 * x) * κ := by
      rw [e, map_mul, map_mul, map_inv]; group
    rw [this]
    exact (KA L).mul_mem ((KA L).mul_mem ((KA L).inv_mem hκ) γ.2) hκ⟩
  invFun γ := ⟨h0⁻¹ * γ.1 * h0, by
    have key : ∀ γ0 : UJ (sp.cm.sig : E →+* E) sp.gram0,
        x⁻¹ * ratA sp (h0⁻¹ * γ0 * h0) * x = κ * (x'⁻¹ * ratA sp γ0 * x') * κ⁻¹ := by
      intro γ0
      rw [e, map_mul, map_mul, map_inv]; group
    rw [key]
    exact (KA L).mul_mem ((KA L).mul_mem hκ γ.2) ((KA L).inv_mem hκ)⟩
  left_inv γ := Subtype.ext (by show h0⁻¹ * (h0 * γ.1 * h0⁻¹) * h0 = γ.1; group)
  right_inv γ := Subtype.ext (by show h0 * (h0⁻¹ * γ.1 * h0) * h0⁻¹ = γ.1; group)

def stabRec (c : C.cls 0) : C.stab 0 c ≃ StabU L (L.y c) :=
  Equiv.ofBijective (fun s => ⟨L.stabI c s, by
      have h := (L.stabI_range c (L.stabI c s : GL (Fin R.k) E) (L.stabI c s).2).1 ⟨s, rfl⟩
      exact (mem_map_conj L.U _ _).1 h⟩)
    ⟨fun a b hab => L.stabI_inj c (congrArg Subtype.val hab), fun γ => by
      obtain ⟨s, hs⟩ := (L.stabI_range c (γ.1 : GL (Fin R.k) E) γ.1.2).2 ((mem_map_conj L.U _ _).2 γ.2)
      exact ⟨s, Subtype.ext hs⟩⟩

def clsOf (L : ColLevel R F E sp gp C A clsLat) (c : ClassSet (HA sp) (KA L)) : C.cls 0 :=
  (Equiv.ofBijective _ L.y_bij).symm c

theorem clsOf_spec (c : ClassSet (HA sp) (KA L)) : Fib.mkC (HA sp) (KA L) (L.y (clsOf L c)) = c :=
  (Equiv.ofBijective _ L.y_bij).apply_symm_apply c

theorem clsOf_inj : Function.Injective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.injective

theorem clsOf_surj : Function.Surjective (clsOf L) := (Equiv.ofBijective _ L.y_bij).symm.surjective

theorem card_stabU (x : GA sp) : Nat.card (StabU L x) = Nat.card (C.stab 0 (clsOf L (Fib.mkC (HA sp) (KA L) x))) := by
  obtain ⟨h, hh, κ, hκ, e⟩ := (Fib.mk_eq_iff (HA sp) (KA L) _ _).1 (clsOf_spec (L := L) (Fib.mkC (HA sp) (KA L) x))
  obtain ⟨h0, rfl⟩ := exists_ratA h hh
  exact (Nat.card_congr ((stabRec _).trans (stabConj _ x h0 κ hκ e))).symm

variable (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ)
    (lam0 : Fin nV → Fin n' → Fin (m + 1) → ℤ) (dom : ∀ v, IsDominant (lam0 v)) (hk : m + 1 = R.k)
    (I : LocId L p nV W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) (e : ℕ) (hdet : IsUnit sp.gram0.det) (hH : HypAtP I)


include hH in
theorem fix_iff (i : compL L p) (g : Fin nV → GL (Fin (m + 1)) Qq) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    (repP L p i * jQ I hdet hk g)⁻¹ * ratA sp γ * (repP L p i * jQ I hdet hk g) ∈ KA L ↔
      γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (repP L p i).1 ∧
        (fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v)) = tupOf W g := by
  refine ((fibP I hdet hk hH).stab_iff (HA sp) (repP L p) (prP_repP I hk) i g (ratA sp γ) (prP_repP I hk)).trans
    (and_congr (mem_gamC_iff (repP L p i) γ).symm ?_)
  show g⁻¹ * (prP I hk (ratA sp γ) * g) ∈ _ ↔ _
  rw [← tupOf_eq_iff]
  have : tupOf W (prP I hk (ratA sp γ) * g) = fun v => gMap W (prP I hk (ratA sp γ) v) (tupOf W g v) := by
    funext v
    exact gMap_mul W _ _ _
  rw [this]


include hH in
def fixEquiv (i : compL L p) (y : GL (Fin R.k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y = (repP L p i).1)
    (g : Fin nV → GL (Fin (m + 1)) Qq) :
    {γ : gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) y //
      (levC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) hS nV r lam0 dom hk I.iw I.frQ ψ y).smul γ (tupOf W g) = tupOf W g} ≃
      StabU L (repP L p i * jQ I hdet hk g) where
  toFun γ := ⟨γ.1.1, (fix_iff hk I hdet hH i g γ.1.1).2 ⟨hy ▸ γ.1.2, by
    have := γ.2
    rwa [level_action_lattice_eq] at this⟩⟩
  invFun γ := ⟨⟨γ.1, hy ▸ ((fix_iff hk I hdet hH i g γ.1).1 γ.2).1⟩, by
    rw [level_action_lattice_eq]
    exact ((fix_iff hk I hdet hH i g γ.1).1 γ.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Formalism.L2.G.Cmp
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.LatticeComparisonCompatible
section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embFr (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) :
    ((D.fm u).lat 0).V →ₛₗ[D.what₂.embLL] ((D.mem u).C.cls 0 → Fr D 0 (Nat.zero_le _) → ℂ) where
  toFun x := fun cl z => (D.fm u).emb 0 x cl (((T u).val0).eY.symm z)
  map_add' x y := by funext cl z; rw [map_add (f := _)]; rfl
  map_smul' a x := by funext cl z; rw [LinearMap.map_smulₛₗ]; rfl

structure CmpIn (D : D7) (X : Formalism.L2.Herm.Herm0 D) where
  embW : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    D.what₂.LL →+* (D.gat u w hg).Kf
  embW_int : ∀ u w hg (x : D.what₂.LL), (0 : WithTop ℤ) ≤ D.what₂.places.val w x ↔
    embW u w hg x ∈ Set.range (algebraMap (D.gat u w hg).O (D.gat u w hg).Kf)
  B : GL (Fin D.R.k) D.host.E
  B_std : StdB D B
  fr_B : ∀ u w hg, FrRat X u w hg B

variable {X : Formalism.L2.Herm.Herm0 D}

def cmpRec (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((D.fm u).lat 0).V → (D.gat u w hg).Fn :=
  cmpC ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg) (I.embW u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

structure CmpHyp (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  uniq : ∀ u w hg, ValUniq ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
    I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
      (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  li : ∀ u w hg, LinearIndependent (D.gat u w hg).Kf (fun a => cmpRec T Gt I u w hg (((D.fm u).lat 0).b a))

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

def latCmpC (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) : LatCmp D where
  embW := I.embW
  embW_int := I.embW_int
  cmp := fun u w hg => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).toAddMonoidHom
  cmp_smul := fun u w hg a x => (cmpL (e := I.embW u w hg) (H.ex u w hg) (H.uniq u w hg)).map_smulₛₗ a x
  cmp_li := H.li
  cmp_M := H.latM

def latticeComparisonCompatible (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) (H : CmpHyp T Gt I) :
    CmpTied D X T Gt (latCmpC T Gt I H) where
  B := I.B
  B_std := I.B_std
  fr_B := I.fr_B
  tie := fun u w hg => cmpC_tie (tEL D) (H.ex u w hg) (H.pos u w hg) (H.chi u w hg)

end Formalism.L2.G.Cmp

end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfRatInv
section
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems NumberField IsDedekindDomain

section Gen

variable {LL Kf : Type} [Field LL] [Field Kf] (e : LL →+* Kf)
variable {V W T : Type} [AddCommGroup V] [Module LL V] [AddCommGroup W] [Module Kf W]
  (ev : T → W →ₗ[Kf] Kf) (φ : V →+ W)

theorem span_inv (hsep : ∀ F : W, (∀ t, ev t F = 0) → F = 0)
    (hsm : ∀ (a : LL) x, φ (a • x) = e a • φ x) (hval : ∀ x, IsRat e ev (φ x))
    (S : Set (W →ₗ[Kf] W)) (hT : ∀ Tm ∈ S, ∀ x, ∃ y, φ y = Tm (φ x))
    {ξ : W} (hξ : ξ ∈ Submodule.span Kf (Set.range φ)) (hinv : ∀ Tm ∈ S, Tm ξ = ξ) :
    ξ ∈ Submodule.span Kf (φ '' {x | ∀ Tm ∈ S, Tm (φ x) = φ x}) := by
  let _ : Algebra LL Kf := e.toAlgebra
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hξ
  set C : Submodule LL Kf := Submodule.span LL (Set.range fun x : c.support => c x) with hC
  have : FiniteDimensional LL C := FiniteDimensional.span_of_finite LL (Set.finite_range _)
  let κ := Module.finBasis LL C
  have hext : ∀ j, ∃ g : Kf →ₗ[LL] LL, g.comp C.subtype = κ.coord j := fun j => LinearMap.exists_extend (κ.coord j)
  choose π hπ using hext
  have hcx : ∀ x ∈ c.support, c x = ∑ j, e (π j (c x)) * (κ j : Kf) := by
    intro x hx
    have hmem : c x ∈ C := Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
    have h1 := κ.sum_repr ⟨c x, hmem⟩
    have h2 : ∀ j, π j (c x) = κ.repr ⟨c x, hmem⟩ j := fun j => by
      have := LinearMap.congr_fun (hπ j) ⟨c x, hmem⟩
      simpa using this
    conv_lhs => rw [show c x = ((⟨c x, hmem⟩ : C) : Kf) from rfl, ← h1]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2, Submodule.coe_smul, Algebra.smul_def]
    rfl
  let ξj : Fin (Module.finrank LL C) → V := fun j => c.sum fun x a => π j a • x
  have hdec : (c.sum fun x a => a • φ x) = ∑ j, (κ j : Kf) • φ (ξj j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ξj, Finsupp.sum, map_sum, hsm, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    have h1 : c x • φ x = ∑ j, ((κ j : Kf) * e (π j (c x))) • φ x := by
      conv_lhs => rw [hcx x hx]
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    exact h1
  rw [hdec]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ξj j, ?_, rfl⟩)
  intro Tm hTm

  choose y hy using hT Tm hTm
  have hzero : ∑ j, (κ j : Kf) • φ (y (ξj j) - ξj j) = 0 := by
    simp only [map_sub, hy, smul_sub, Finset.sum_sub_distrib]
    have h2 : ∑ x, (κ x : Kf) • Tm (φ (ξj x)) = Tm (∑ x, (κ x : Kf) • φ (ξj x)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun x _ => (map_smul Tm _ _).symm
    rw [h2, ← hdec, hinv Tm hTm, sub_self]
  have hli : LinearIndependent LL fun j => (κ j : Kf) :=
    κ.linearIndependent.map' C.subtype (Submodule.ker_subtype C)
  have hφz : φ (y (ξj j) - ξj j) = 0 := by
    refine hsep _ fun t => ?_
    choose q hq using fun j' => hval (y (ξj j') - ξj j') t
    have h3 := congrArg (ev t) hzero
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h3
    simp only [map_smul, smul_eq_mul, ← hq] at h3
    have h4 : ∑ j', q j' • (κ j' : Kf) = 0 := by
      rw [← h3]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [Algebra.smul_def, mul_comm]
      rfl
    have h5 := Fintype.linearIndependent_iff.1 hli q h4 j
    rw [← hq, h5, map_zero]
  rw [map_sub, sub_eq_zero, hy] at hφz
  exact hφz

end Gen

section Inv

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] [NumberField LL] (e : LL →+* G.Kf)

def evX (m : (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) →₀ ℕ) :
    G.P.Xsp →ₗ[G.Kf] G.Kf := MvPolynomial.lcoeff G.Kf m

theorem evX_sep (F : G.P.Xsp) (h : ∀ m, evX G m F = 0) : F = 0 := by
  exact MvPolynomial.ext F 0 fun m => by simpa [evX] using h m

theorem map_e_smul (a : LL) (Q : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :
    MvPolynomial.map e (a • Q) = e a • MvPolynomial.map e Q := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

theorem map_e_rat (Q : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :
    IsRat e (evX G) (MvPolynomial.map e Q) := fun m => ⟨Q.coeff m, by simp [evX, MvPolynomial.coeff_map]⟩

theorem inv_span [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hA : RatActG G e) (i : G.comp) (L0 : G.P.Tup) (hB : RatBasisAt G e L0)
    (ξ : G.P.Xsp) (hξ : ξ ∈ G.P.HtupW L0) (hI : InvAt G i L0 ξ) :
    ξ ∈ Submodule.span G.O {ξ' | ξ' ∈ G.P.HtupW L0 ∧ InvAt G i L0 ξ' ∧ RatX G e ξ'} := by
  let φ : MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL →+ G.P.Xsp :=
    (MvPolynomial.map e).toAddMonoidHom
  have hφ : ∀ (a : LL) Q, φ (a • Q) = e a • φ Q := map_e_smul G e

  let Lr : Submodule (𝓞 LL) (MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :=
    { carrier := {Q | MvPolynomial.map e Q ∈ G.P.HtupW L0}
      add_mem' := by
        intro Q Q' h h'
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at h h' ⊢
        exact Submodule.add_mem _ h h'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        exact Submodule.zero_mem _
      smul_mem' := by
        intro a Q h
        simp only [Set.mem_ofPred_eq] at h ⊢
        obtain ⟨o, ho⟩ := (hσ (algebraMap (𝓞 LL) LL a)).1 (w.valuation_le_one a)
        have : MvPolynomial.map e (a • Q) = o • MvPolynomial.map e Q := by
          rw [← algebraMap_smul G.Kf o, ho, ← map_e_smul G e, algebraMap_smul]
          rfl
        convert Submodule.smul_mem _ o h using 1
        exact this }

  let Ur : Submodule LL (MvPolynomial (Σ v : Fin G.P.nV, Fin (G.P.n' v) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) LL) :=
    { carrier := {Q | InvAt G i L0 (MvPolynomial.map e Q)}
      add_mem' := fun {Q Q'} h h' γ hγ => by
        rw [map_add (f := _), map_add (f := _), smul_add, h γ hγ, h' γ hγ]
      zero_mem' := fun γ _ => by rw [map_zero, map_zero, smul_zero]
      smul_mem' := fun a Q h γ hγ => by
        show ((G.lev i).χ γ : G.O) • (G.lev i).actX γ (MvPolynomial.map e (a • Q)) = MvPolynomial.map e (a • Q)
        rw [map_e_smul, map_smul, smul_comm, h γ hγ] }

  have h1 : ξ ∈ Submodule.span G.O (φ '' (Lr : Set _)) := by
    refine Submodule.span_mono ?_ (htupW_rat G e L0 hB hξ)
    rintro _ ⟨hx, Q, rfl⟩
    exact ⟨Q, hx, rfl⟩

  let S : Set (G.P.Xsp →ₗ[G.Kf] G.P.Xsp) := {Tm | ∃ γ : (G.lev i).Γ, (G.lev i).smul γ L0 = L0 ∧
    Tm = (algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)) • (G.lev i).actX γ}
  have hTm : ∀ γ (X : G.P.Xsp), ((algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)) • (G.lev i).actX γ) X =
      ((G.lev i).χ γ : G.O) • (G.lev i).actX γ X := fun γ X => by
    rw [LinearMap.smul_apply, algebraMap_smul]
  have h2 : ξ ∈ Submodule.span G.Kf (φ '' (Ur : Set _)) := by
    have hspan : ξ ∈ Submodule.span G.Kf (Set.range φ) := by
      have : Submodule.span G.O (φ '' (Lr : Set _)) ≤ (Submodule.span G.Kf (Set.range φ)).restrictScalars G.O := by
        rw [Submodule.span_le]
        rintro _ ⟨Q, _, rfl⟩
        exact Submodule.subset_span ⟨Q, rfl⟩
      exact this h1
    have := span_inv e (evX G) φ (evX_sep G) hφ (map_e_rat G e) S (by
        rintro Tm ⟨γ, _, rfl⟩ Q
        obtain ⟨Q', hQ'⟩ := hA i γ (MvPolynomial.map e Q) ⟨Q, rfl⟩
        exact ⟨Q', by rw [hTm]; exact hQ'⟩)
      hspan (by
        rintro Tm ⟨γ, hγ, rfl⟩
        rw [hTm]; exact hI γ hγ)
    refine Submodule.span_mono ?_ this
    rintro _ ⟨Q, hQ, rfl⟩
    refine ⟨Q, fun γ hγ => ?_, rfl⟩
    have := hQ _ ⟨γ, hγ, rfl⟩
    rw [hTm] at this
    exact this

  have hb : LinearIndependent G.Kf (φ ∘ (MvPolynomial.basisMonomials _ LL)) := by
    have e1 : φ ∘ (MvPolynomial.basisMonomials _ LL) = MvPolynomial.basisMonomials _ G.Kf := by
      funext m
      simp [φ, MvPolynomial.coe_basisMonomials]
    rw [e1]
    exact (MvPolynomial.basisMonomials _ G.Kf).linearIndependent
  have h3 := (Formalism.BasicNotions.FBC.flat_ext w e hσ φ hφ (MvPolynomial.basisMonomials _ LL) hb).2 Lr Ur
  have h4 : ξ ∈ Submodule.span G.O (φ '' ((Lr ⊓ Ur.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) _) : Set _)) := by
    rw [← h3]
    exact ⟨h1, h2⟩
  refine Submodule.span_mono ?_ h4
  rintro _ ⟨Q, ⟨hQ1, hQ2⟩, rfl⟩
  exact ⟨hQ1, hQ2, Q, rfl⟩

theorem hRatInv_of [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (hA : RatActG G e) (hB : RatBasis G e) : HRatInv G e :=
  fun i L0 hL0 ξ hξ => inv_span G e w hσ hA i L0 (hB L0 hL0) ξ hξ.1 hξ.2

theorem mRatSpan_of_rat_inv [IsFractionRing G.O G.Kf] (w : HeightOneSpectrum (𝓞 LL))
    (hσ : ∀ x : LL, w.valuation LL x ≤ 1 ↔ e x ∈ Set.range (algebraMap G.O G.Kf)) (h2 : G.FinClasses) (hL : RatLev G e) (hB : RatBasis G e) :
    MRatSpan G.P G.comp e G.M :=
  mRatSpan_inv G e h2 (Formalism.L2.G.Cmp.equivSys_HtupW G) (ratActG_of G e hL) (hRatInv_of G e w hσ (ratActG_of G e hL) hB)

end Inv

end Formalism.L2.G.Cmp
end
end

