module Choice = Choice

module type MODEL = sig
  (** The model's internal state. *)
  type t

  (** Commands that the model can execute. *)
  type cmd

  (** Responses that can arise from executing a command. *)
  type res

  (** Errors that may be returned by the model because a command cannot be executed
      in the current (model) state. *)
  type error

  val step : t -> cmd -> res -> (t, error) result
  (** The model's transition function. Given a command of type [cmd] and the concrete
      result [res], [step] updates the model's state. [res] can often be [unit], but
      some fuzzers benefit from delegating the computing of some parts of the state to
      the concrete implementation. It returns an error when [cmd] and [res] are
      incompatible with the current state. *)

  val init : t
  (** The model's (default) initial state. *)
end

module type CONCRETE = sig
  module Model : MODEL

  (** The concrete implementation's internal state. *)
  type t

  (** Errors that may be returned by the implementation, either because a command
      cannot be executed in the current (concrete) state or because the model's
      state has diverged from the implementation's. *)
  type error

  val exec : Model.cmd -> t -> (Model.res * t, error) result
  (** The implementation's transition function. Given a command of type [cmd], [exec]
      maps a concrete state to the next concrete state and a concrete result that can
      be used to update the abstract model. *)

  val check : Model.t -> t -> (unit, error) result
  (** Check whether the implementation and model have diverged. *)

  val init : t
  (** The concrete implementation's (default) initial state.
      This should satisfy [check Model.init init = Ok ()]. *)
end

