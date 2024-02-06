let preamble = ref false

let speclist =
  [("-add-preambles", Arg.Set preamble, "Add preambles to generated mlw")]
