module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

structure CmpHyp0P (T : ∀ u : D.what₂.Word, Forms0 D u) (Gt : GatTies D) (I : CmpIn D X) : Prop where

  ex : ∀ u w hg, ValEx ((T u).cls0).lev (embT D) D.what₂.embLL (D.gat u w hg)
    (locAt X u w hg I.B) (Gt.gat_pos u w hg) (embFr T u) ((T u).cls0).y

  evInj : ∀ u w hg, EvInj (embT D) (D.gat u w hg) (locAt X u w hg I.B) (Gt.gat_pos u w hg)
    (J := gramN D 0 (Nat.zero_le _))

  ptEx : ∀ u w hg, PtEx ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B)
    ((T u).cls0).y

  ptAll : ∀ u w hg, PtAll ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg I.B)
    ((T u).cls0).y

  chi : ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

  latM : ∀ u w hg, Submodule.span (D.gat u w hg).O
    (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M

theorem CmpHyp0P.toHyp0 {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X} (H : CmpHyp0P T Gt I)
    (pos : ∀ u w hg v (s : Fin ((D.gat u w hg).P.n' v)) (x : D.host.E),
      I.embW u w hg (tEL D (Gt.gat_pos u w hg ⟨v, s⟩) (if Even s.val then x else sigD D x)) =
        (D.gat u w hg).P.ι v (((D.gat u w hg).P.σ v ^ s.val) ((locAt X u w hg I.B).iw v x))) : Cmp.CmpHyp0 T Gt I := by
  exact Cmp.CmpHyp0.mk H.ex H.evInj H.ptEx H.ptAll pos H.chi H.latM

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CompanionOfBaseTied
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.G

section Re

theorem reGL_mulVec {a b : ℕ} (h : a = b) {E : Type} [Field E] (M : GL (Fin a) E) (x : Fin a → E) (i : Fin b) :
    ((reGL h E M).1 *ᵥ fun j : Fin b => x (Fin.cast h.symm j)) i = (M.1 *ᵥ x) (Fin.cast h.symm i) := by
  subst h
  rw [reGL_rfl]
  rfl

end Re

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdB_mem (D : D7) (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (x : Fin D.R.k → D.host.E) :
    x ∈ D.sp.crdLat0 (D.sp.X 0).L0 ↔
      ∀ a, ((B⁻¹ : GL (Fin D.R.k) D.host.E).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h2 := hB.2 (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j))
  have e1 : (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j)) ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔ x ∈ D.sp.crdLat0 (D.sp.X 0).L0 := by
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext a
      have := congrFun e (Fin.cast (rank_eq_first_level D.R) a)
      exact this
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext j
      have := congrFun e (Fin.cast (rank_eq_first_level D.R).symm j)
      exact this
  rw [← e1, h2]
  constructor
  · intro h a
    have := h (Fin.cast (rank_eq_first_level D.R) a)
    rw [← map_inv, reGL_mulVec] at this
    exact this
  · intro h j
    rw [← map_inv, reGL_mulVec]
    exact h _

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem T_smul_mem (L : ColLevel R F E sp gp C A clsLat) (y : Fin R.k → E)
    (hy : y ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)) : (A.T : E) • y ∈ L.Lb := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact L.Lb_dual y hy
  | zero => rw [smul_zero]; exact L.Lb.zero_mem
  | add y z _ _ h1 h2 => rw [smul_add]; exact L.Lb.add_mem h1 h2
  | smul c y _ h => rw [smul_comm]; exact L.Lb.smul_mem c h

theorem companion_le (L : ColLevel R F E sp gp C A clsLat) (𝔞 : Ideal (𝓞 E)) :
    L.Lb ⊔ 𝔞 • Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) ≤
      Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) :=
  sup_le (fun x hx => Submodule.subset_span (L.Lb_int x hx)) Submodule.smul_le_right

def LocId.withFr (I : LocId L p nV W Qq) (B : GL (Fin R.k) E)
    (h1 : ∀ x ∈ L.Lb, ∀ a, ((B⁻¹ : GL (Fin R.k) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (N : ℕ) (hN : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → (N : 𝓞 F) ∉ w.asIdeal)
    (h2 : ∀ i, (N : E) • (B.1 *ᵥ Pi.single i 1) ∈ L.Lb) : LocId L p nV W Qq :=
  { I with
    fr := fun w h => bc (((RingHom.fst _ _).comp (I.spl w h).toRingHom).comp (inclE (F := F) (w.adicCompletion F))) B
    fr_lat := fun w h t => Formalism.MainNotions.Gaps.Loc.fr_lat_of w (I.spl w h) (I.spl_alg w h) L.Lb B h1 N (hN w h) h2 t }

def locIdStd (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq')
    (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (𝔞 : Ideal (𝓞 D.host.E))
    (hL : Lc.Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 Lc.Lb) =
      D.sp.crdLat0 (D.sp.X 0).L0) : LocId Lc (D.what₂.places.resChar w) nV W' Qq' :=
  I.withFr B (fun x hx => (stdB_mem D B hB x).1 (hL ▸ (le_sup_left : Lc.Lb ≤ _) hx)) (D.mem u).A.T
    (fun w' hw' => natCast_notMem w' hg.1 hw' hg.2.2.2.2.2)
    (fun i => T_smul_mem Lc _ (companion_le Lc 𝔞 (hL ▸ (stdB_mem D B hB _).2 fun a => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : a = i
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩)))

theorem companion_of_baseTied (D : D7) (H : Formalism.L2.Herm.HermCols D) (aT : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u))
    (hb : Formalism.L2.Herm.BaseTied D H aT) (u : D.what₂.Word) :
    ∃ 𝔞 : Ideal (𝓞 D.host.E), (H.lev0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
      (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0 := by
  have hi : IsIntegral ℤ (D.host.conj ((aT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  exact ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (hb u ⟨_, hi⟩ rfl).1⟩

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsi
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

def PsiTied {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) (hk : R.k = n)
    {LL O Kf : Type} [Field LL] [CommRing O] [Field Kf] [Algebra O Kf] (embLL : LL →+* ℂ) (e : LL →+* Kf)
    (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ) : Prop :=
  ∀ (a : Formalism.L2.Herm.awayFrom₂ L p) (κ : S.U),
    (∀ v : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → bc (prV (E := E) v) κ.1 = 1) →
    (∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal →
      bc (prV (E := E) w) κ.1 = bc (prV (E := E) w) (reGL hk _ a.1)) →
    ∃ r : LL, embLL r = (S.chi κ : ℂ) ∧ algebraMap O Kf ((ψ a : Oˣ) : O) * e r = 1

end Gen

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)


set_option maxHeartbeats 4000000 in
theorem chi_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E)
    (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (hL : X.lev0 u = L)
    (ψ : Formalism.L2.Herm.awayFrom₂ L (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ)
    (hχ : ∀ i (γ : ((D.gat u w hg).lev i).Γ) (a : Formalism.L2.Herm.awayFrom₂ L (D.what₂.places.resChar w)),
      a.1 = (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
        ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 → ((D.gat u w hg).lev i).χ γ = ψ a)
    (hψ : PsiTied ((T u).cls0).lev L (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL e ψ)
    (i : (D.gat u w hg).comp) (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U)
    (hκ : (locAt X u w hg B).IsAway i γ κ.1) :
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * e r = 1 := by
  subst hL
  have h1 : (((X.g u w hg).yG i).1)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1 ∈ Formalism.L2.Herm.awayFrom₂ (X.lev0 u) (D.what₂.places.resChar w) :=
    (mem_map_conj _ _ _).1 (((X.g u w hg).gamI_range i _).1 ⟨γ, rfl⟩)
  have ee : ((locAt X u w hg B).yG i)⁻¹ * bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ((locAt X u w hg B).gamI i γ) * (locAt X u w hg B).yG i = reGL (rank_eq_first_level D.R) _ ((((X.g u w hg).yG i).1)⁻¹ *
        bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((X.g u w hg).gamI i γ).1 * ((X.g u w hg).yG i).1) := by
    rw [map_mul, map_mul, map_inv, ← bc_reGL]
    rfl
  rw [hχ i γ ⟨_, h1⟩ rfl]
  refine hψ ⟨_, h1⟩ κ (fun v hv => ?_) (fun w' hw' => ?_)
  · obtain ⟨v', rfl⟩ := LocGood.exists_pl (locAt X u w hg B) v hv
    exact hκ.1 v'
  · rw [hκ.2 w' hw', ee]

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Gen

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def HypT {L : ColLevel R F E sp gp C A clsLat} (t : Formalism.L2.Herm.GLevTie L G) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) (x : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)),
    x ∈ UPts sp.cm.sig sp.gram0 (w.adicCompletion F) →
    (∀ a b, (((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) →
    (∀ a b, ((((t.fr w h)⁻¹ * bc ((RingHom.fst _ _).comp (t.spl w h).toRingHom) x * t.fr w h)⁻¹ : GL (Fin R.k) _) :
      Matrix (Fin R.k) (Fin R.k) _) a b ∈ w.adicCompletionIntegers F) → x ∈ L.Uloc w

theorem hypT_of {L L' : ColLevel R F E sp gp C A clsLat} (hL : L' = L) (t : Formalism.L2.Herm.GLevTie L' G) {nV : ℕ} {W Qq : Type}
    [CommRing W] [Field Qq] [Algebra W Qq] (I : LocId L p nV W Qq) (hfr : t.fr = I.fr) (hspl : t.spl = I.spl)
    (hH : HypAtP I) : HypT t := by
  subst hL
  intro w h x hx h1 h2
  rw [hfr, hspl] at h1 h2
  obtain ⟨v, rfl⟩ : ∃ v, I.plc v = w := ⟨I.pl.symm ⟨w, h⟩, by simp [LocId.plc]⟩
  exact (hH v x hx).2 ⟨h1, h2⟩

theorem reGL_symm_mem_UPts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (σ : E →ₐ[F] E) (J : Matrix (Fin a) (Fin a) E)
    (J' : Matrix (Fin b) (Fin b) E) (hJ : ∀ x y, J' x y = J (Fin.cast h.symm x) (Fin.cast h.symm y))
    (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin b) (E ⊗[F] R)) (hg : g ∈ UPts σ J' R) :
    (reGL h _).symm g ∈ UPts σ J R := by
  subst h
  have : J' = J := by ext x y; exact hJ x y
  rw [this] at hg
  have e : (reGL (rfl : a = a) (E ⊗[F] R)).symm g = g := by
    apply (reGL (rfl : a = a) (E ⊗[F] R)).injective
    rw [MulEquiv.apply_symm_apply, reGL_rfl]
  rw [e]; exact hg

end Gen

variable {D : D7} (X : Formalism.L2.Herm.Herm0 D)

theorem locInt_locAt (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) : LocInt (locAt X u w hg B) :=
  fun v x => (X.g u w hg).completion_integers_iff v _ rfl x

set_option maxHeartbeats 4000000 in
theorem locHyp_locAt (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B)
    (hT : HypT (X.g u w hg)) : LocHyp ((T u).cls0).lev (locAt X u w hg B) := by
  refine locHyp_of (rank_eq_first_level D.R) (locAt X u w hg B) _ D.sp.gram0 (gramN_zero D) B rfl
    (fun v => (X.lev0 u).Uloc v) hU ?_
  intro v x0 hx0 h1 h2
  have hfr := hB _ ((X.g u w hg).pl v).2
  refine hT _ ((X.g u w hg).pl v).2 x0 hx0 ?_ ?_
  · rw [hfr]; exact h1
  · rw [hfr]; exact h2

theorem bad_notOver (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (hw : w' ∈ badG D) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ w'.asIdeal := by
  intro hv
  have hp : (D.what₂.places.resChar w).Prime := hg.1
  have hg' : ∀ i, ¬ D.what₂.places.resChar w ∣ D.host.g i := fun i hd =>
    hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hp (D.host.g_prime i)).1 hd) ▸ D.host.g_level i)
  rcases hw with h | h
  · exact natCast_notMem _ hp hv (hg' 0) h
  · exact natCast_notMem _ hp hv (hg' 1) h


set_option maxHeartbeats 4000000 in
theorem ptOne_rec (T : ∀ u : D.what₂.Word, Forms0 D u) (u : D.what₂.Word) (hU : SameUloc X T u) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B : GL (Fin D.R.k) D.host.E) (hB : FrRat X u w hg B)
    (hT : HypT (X.g u w hg)) : PtOne ((T u).cls0).lev (D.gat u w hg) (locAt X u w hg B) :=
  ptOne_of _ (locInt_locAt X u w hg B) (locHyp_locAt X T u hU w hg B hB hT)
    (bad_notOver u w hg)

end Formalism.L2.G
end
end

