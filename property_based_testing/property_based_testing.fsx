#r "nuget: FsCheck, 3.0.0-alpha4"

open FsCheck

type Post = { id: int; authorId: int } // this post contains the common fields to all kinds of posts
type OriginalPost = { id: int; body: string } // this post contains original text
type Repost = { id: int; originalPostId: int } // this post is from another author and contains a link to the original post
type Author = { id: int; name: string }

type Request =
    | PostReq of (OriginalPost * Post)
    | RepostReq of (Repost * Post)

type Database =
    { posts: Post list
      originals: OriginalPost list
      reposts: Repost list
      authors: Author list }

// Properties:
// 0 for each original post there is a corresponding post
// 1 for each repost there is a corresponding post
// 2 for each post there's a corresponding author

let serve (db: Database) (xs: Request seq) =
    let prop0 (o: OriginalPost) (p: Post) = o.id = p.id
    let prop1 (r: Repost) (p: Post) = r.id = p.id

    let prop2 (p: Post) =
        db.authors |> List.exists (fun author -> author.id = p.authorId)

    xs
    |> Seq.fold
        (fun (db: Database) ->
            function
            | PostReq(o, p) when prop0 o p && prop2 p ->
                { db with
                    originals = o :: db.originals
                    posts = p :: db.posts }
            | RepostReq(r, p) when prop1 r p && prop2 p ->
                { db with
                    posts = p :: db.posts
                    reposts = r :: db.reposts }
            | _ -> db)
        db

// generate a database with 0 to 10 posts
let genDb =
    let genAuthor =
        Arb.generate<int * string>
        |> Gen.map (fun (id, name) -> { id = id; name = name })

    let genId = Arb.generate<int>

    let genPost (author: Gen<Author>) =
        Gen.zip genId author
        |> Gen.map (fun (id, author) -> { id = id; authorId = author.id })

    let genBody = Arb.generate<string>

    // this original post holds the property 0
    let genOriginalPost (post: Gen<Post>) =
        Gen.zip genBody post
        |> Gen.map (fun (body, post) -> PostReq({ id = post.id; body = body }, post))

    let genRepost (post: Gen<Post>) =
        Gen.zip genId post
        |> Gen.map (fun (id, post) -> RepostReq({ id = id; originalPostId = post.id }, post))

    let oneof (xs: 'a list) =
        Gen.choose (0, (xs.Length - 1)) |> Gen.map (fun i -> xs[i])

    gen {
        let! authors = Gen.listOfLength 10 genAuthor
        let! validPosts = oneof authors |> genPost |> Gen.listOfLength 30
        let! originalPosts_hold0 = oneof validPosts |> genOriginalPost |> Gen.listOf
        let! originalPosts_violate0 = oneof authors |> genPost |> genOriginalPost |> Gen.listOf
        let! originalPosts_violate2 = genAuthor |> genPost |> genOriginalPost |> Gen.listOf

        let! reposts_hold1 = oneof validPosts |> genRepost |> Gen.listOf
        let! reposts_violate1 = oneof authors |> genPost |> genRepost |> Gen.listOf
        let! reposts_violate2 = genAuthor |> genPost |> genRepost |> Gen.listOf

        let! requests =
            originalPosts_hold0
            @ originalPosts_violate0
            @ originalPosts_violate2
            @ reposts_hold1
            @ reposts_violate1
            @ reposts_violate2
            |> Gen.shuffle

        let db =
            serve
                { posts = []
                  originals = []
                  reposts = []
                  authors = authors }
                requests

        return db

    }


let existsPost (db: Database) (id: int) =
    db.posts |> List.exists (fun p -> p.id = id)

let prop0 db =
    db.originals |> List.forall (existsPost db << _.id)

let prop1 db =
    db.reposts |> List.forall (existsPost db << _.id)

let existsAuthor (db: Database) (id: int) =
    db.authors |> List.exists (fun a -> a.id = id)

let prop2 db =
    db.posts |> List.forall (fun p -> existsAuthor db p.authorId)

let testDb = Arb.fromGen genDb

[ prop0; prop1; prop2 ]
|> List.map (fun p -> Prop.forAll testDb p)
|> List.iter Check.Quick
