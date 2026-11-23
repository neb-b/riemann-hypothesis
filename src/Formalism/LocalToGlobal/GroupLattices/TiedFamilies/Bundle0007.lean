module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.TiedRec
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0008
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

def levTieOf {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    Formalism.L2.Herm.GLevTie L' G :=
  h ▸ t

theorem levTieOf_fr {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).fr = t.fr := by
  subst h
  rfl

theorem levTieOf_spl {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).spl = t.spl := by
  subst h
  rfl

end Cast

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)

def packC : ∀ u (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    LocPack D u (Lc u) (D.what₂.places.resChar w) :=
  fun u w h => locPackC D u (Lc u) w h.2.1 (nFr_spec D h).1 (nFr_spec D h).2 (I u w h) (ψ u w h)

variable (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev recC : D7 := recG D sc Ce Lc (packC D Lc I ψ) hd

abbrev gatTiesC : GatTies (recC D sc Ce Lc I ψ hd) := gatTiesG D sc Ce Lc (packC D Lc I ψ) hd


set_option maxHeartbeats 4000000 in
theorem ringTied_recC (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (v : Fin ((recC D sc Ce Lc I ψ hd).gat u w hg).P.nV) : RingCompatibleAt (recC D sc Ce Lc I ψ hd) u w hg v := by
  unfold RingCompatibleAt
  exact ⟨RingEquiv.refl (((recC D sc Ce Lc I ψ hd).gat u w hg).P.W v),
    RingEquiv.refl (((recC D sc Ce Lc I ψ hd).gat u w hg).P.Qq v),
    RingEquiv.refl ((recC D sc Ce Lc I ψ hd).gat u w hg).O, RingEquiv.refl ((recC D sc Ce Lc I ψ hd).gat u w hg).Kf,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

def hermitianLevelZeroOfRecursion (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u) :
    Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd) :=
  { H0 with g := fun u w hg => levTieOf (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg) }

theorem gatIs_recC (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (hH : ∀ u w h, Cmp.HypAtP (I u w h)) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    GatIs (recC D sc Ce Lc I ψ hd) (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).lev0 u w hg := by
  exact gatIs_recG D sc Ce Lc (packC D Lc I ψ) hd _ hL hH u w hg


set_option maxHeartbeats 4000000 in
theorem frRat_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Cmp.FrRat (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B := by
  intro w' h
  dsimp only [hermitianLevelZeroOfRecursion]
  erw [levTieOf_fr (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg),
    levTieOf_spl (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg)]
  exact hB u w hg w' h


set_option maxHeartbeats 4000000 in
def cmpInC (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B) :
    Cmp.CmpIn (recC D sc Ce Lc I ψ hd) (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) where
  embW := fun _ w _ => embRec (recC D sc Ce Lc I ψ hd) w (nFr D (D.what₂.places.resChar w))
  embW_int := fun _ w _ x => embRec_int (recC D sc Ce Lc I ψ hd) w (nFr D (D.what₂.places.resChar w)) x
  B := B
  B_std := hBs
  fr_B := fun u w hg => frRat_C D sc Ce Lc I ψ hd H0 hL B hB u w hg


set_option maxHeartbeats 4000000 in
def groupCompatibilityOfRecursion (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (CH : Cmp.CmpHyp T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB))
    (hH : ∀ u w h, Cmp.HypAtP (I u w h)) :
    GroupCompatibilityAll (recC D sc Ce Lc I ψ hd) (gatTiesC D sc Ce Lc I ψ hd)
      (Cmp.latCmpC T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) CH) where
  herm := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL
  forms := T
  cmp := Cmp.latticeComparisonCompatible T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) CH
  ring := ringTied_recC D sc Ce Lc I ψ hd
  gat := gatIs_recC D sc Ce Lc I ψ hd H0 hL hH

end Formalism.L2.G
end
end

-- bundled from Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieWeak
section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Adic

variable {F : Type} [Field F] [NumberField F]

theorem adic_dense (v : HeightOneSpectrum (𝓞 F)) (y c : v.adicCompletion F) (hc : c ≠ 0) :
    ∃ a : F, ∃ z ∈ v.adicCompletionIntegers F, algebraMap F (v.adicCompletion F) a = y + c * z := by
  let U : Set (v.adicCompletion F) :=
    (fun x => c⁻¹ * (x - y)) ⁻¹' ((v.adicCompletionIntegers F) : Set (v.adicCompletion F))
  have hU : IsOpen U := (Valued.isOpen_integer (v.adicCompletion F)).preimage
    (continuous_const.mul (continuous_id.sub continuous_const))
  have hU' : U.Nonempty := ⟨y, by
    simp only [U, Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
    exact zero_mem _⟩
  obtain ⟨a, ha⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (v := v)).exists_mem_open hU hU'
  refine ⟨a, _, ha, ?_⟩
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  ring

theorem adic_dist (v v' : HeightOneSpectrum (𝓞 F)) (h : v ≠ v') :
    ∃ a : F, algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F ∧
      algebraMap F (v'.adicCompletion F) a ∉ v'.adicCompletionIntegers F := by
  have hb : ∃ b ∈ v'.asIdeal, b ∉ v.asIdeal := by
    by_contra hcon
    push Not at hcon
    have hle : v'.asIdeal ≤ v.asIdeal := fun b hb => hcon b hb
    exact h (HeightOneSpectrum.ext (v'.isMaximal.eq_of_le v.isPrime.ne_top hle)).symm
  obtain ⟨b, hb', hb⟩ := hb
  have hb0 : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h0
    have : b = 0 := (FaithfulSMul.algebraMap_injective (𝓞 F) F) (by rw [h0, map_zero])
    exact hb (this ▸ v.asIdeal.zero_mem)
  refine ⟨(algebraMap (𝓞 F) F b)⁻¹, ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F b)⁻¹) =
        v.valuation F (algebraMap (𝓞 F) F b)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v _
    rw [e, map_inv₀]
    have h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1 :=
      le_antisymm (v.valuation_le_one b) (not_lt.1 fun hlt => hb ((v.valuation_lt_one_iff_mem (K := F) b).1 hlt))
    rw [h1, inv_one]
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have e : Valued.v (algebraMap F (v'.adicCompletion F) (algebraMap (𝓞 F) F b)⁻¹) =
        v'.valuation F (algebraMap (𝓞 F) F b)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v' _
    rw [e, map_inv₀, not_le]
    have h1 : v'.valuation F (algebraMap (𝓞 F) F b) < 1 := (v'.valuation_lt_one_iff_mem (K := F) b).2 hb'
    have h2 : v'.valuation F (algebraMap (𝓞 F) F b) ≠ 0 := (Valuation.ne_zero_iff _).2 hb0
    exact (one_lt_inv₀ (zero_lt_iff.2 h2)).2 h1

end Adic

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ}

theorem weak_of_locAt (G : GAtP p) (A : LocAt F E n G)
    (hF : ∀ v (a : F), A.iw v (algebraMap F E a) = (A.eQ v).symm (algebraMap F ((A.pl v).1.adicCompletion F) a))
    (hW : ∀ v (x : G.P.Qq v), x ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ↔
      A.eQ v x ∈ (A.pl v).1.adicCompletionIntegers F) : WeakApprox G A.iw := by
  have hp : ∀ v, ((p : ℕ) : G.P.Qq v) ≠ 0 := by
    intro v h0
    have hS := G.P.setting v
    have := hS.frac_alt
    have h1 : algebraMap (G.P.W v) (G.P.Qq v) ((p : ℕ) : G.P.W v) = 0 := by
      rw [map_natCast]; exact h0
    exact hS.p_unif.ne_zero ((IsFractionRing.injective (G.P.W v) (G.P.Qq v)) (by rw [h1, map_zero]))
  refine weakApprox_of_approx_and_separation G A.iw (fun v => (G.P.setting v).frac_alt) hp (fun v => (G.P.setting v).p_unif.not_isUnit) ?_ ?_
  · intro v x N
    have hc : (((p : ℕ) : (A.pl v).1.adicCompletion F)) ^ N ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [← map_natCast (A.eQ v)]
      exact (map_ne_zero_iff _ (A.eQ v).injective).2 (hp v)
    obtain ⟨a, z, hz, e⟩ := adic_dense (A.pl v).1 (A.eQ v x) _ hc
    obtain ⟨c, hcc⟩ := (hW v ((A.eQ v).symm z)).2 (by rw [RingEquiv.apply_symm_apply]; exact hz)
    refine ⟨algebraMap F E a, c, ?_⟩
    rw [hF, e, map_add (f := _), map_mul, map_pow, RingEquiv.symm_apply_apply, hcc, map_natCast]
  · intro v v' hne
    obtain ⟨a, h1, h2⟩ := adic_dist (A.pl v).1 (A.pl v').1 (fun h => hne (A.pl.injective (Subtype.ext h)))
    refine ⟨algebraMap F E a, ?_, ?_⟩
    · rw [hF]
      refine (hW v _).2 ?_
      rw [RingEquiv.apply_symm_apply]; exact h1
    · rw [hF]
      intro hm
      have h3 := (hW v' _).1 hm
      rw [RingEquiv.apply_symm_apply] at h3
      exact h2 h3

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D}

theorem locAt_iw_F (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (B : GL (Fin D.R.k) D.host.E) (v : Fin (D.gat u w hg).P.nV) (a : D.host.F) :
    (locAt X u w hg B).iw v (algebraMap D.host.F D.host.E a) =
      ((locAt X u w hg B).eQ v).symm (algebraMap D.host.F (((locAt X u w hg B).pl v).1.adicCompletion D.host.F) a) :=
  congrArg ((locAt X u w hg B).eQ v).symm ((X.g u w hg).spl_F _ ((X.g u w hg).pl v).2 a)

theorem weakRec_pf (I : CmpIn D X) : WeakRec I := fun u w hg =>
  weak_of_locAt (D.gat u w hg) (locAt X u w hg I.B) (locAt_iw_F u w hg I.B) (fun v x => (X.g u w hg).completion_integers_iff v _ rfl x)

variable {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D} {I : CmpIn D X}

theorem latM_rec' (H : CmpCore T Gt I) (hG : ∀ u w hg, GatIs D X.lev0 u w hg) (hloc : ValIntRec T Gt I)
    (hsurj : SurjRat T Gt I)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Submodule.span (D.gat u w hg).O
      (cmpRec T Gt I u w hg '' (((D.fm u).lat 0).L : Set ((D.fm u).lat 0).V)) = (D.gat u w hg).M :=
  latM_rec H hG hloc hsurj (weakRec_pf I) u w hg

end Formalism.L2.G
end
end

