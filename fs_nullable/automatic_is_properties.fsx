type Contact =
  | Email of address: string
  | Phone of countryCode: int * number: string

type Person = { name: string; contact: Contact }

let john =
  { name = "John"
    contact = Email "john@notX" }

let jane =
  { name = "Jane"
    contact = Phone(48, "393939") }

printfn $"{john.contact.IsEmail} {john.contact.IsPhone}"
// prints "True False"
printfn $"{jane.contact.IsEmail} {jane.contact.IsPhone}"
// prints "False True"
