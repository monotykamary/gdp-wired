export async function create(db: any, id: string, amount: number, active: boolean) {
  await db.account.create({data: {id, amount, active}})
}
export async function update(db: any, id: string, amount: number) {
  await db.account.update({where: {id}, data: {amount}})
}
export async function read(db: any, id: string) {
  const row = await db.account.findUnique({where: {id}})
  return row.amount
}
export async function lookup(repo: any, id: string) {
  const row = await repo.findOneBy({id})
  return row.amount
}

export async function save(repo: any, id: string, amount: number, active: boolean) {
  await repo.save({id, amount, active})
}

export async function unsafeRead(db: any, id: string) {
  const _row = await db.account.findUnique({where: {id}})
  return 0
}
export async function badSave(repo: any, id: string) {
  await repo.save({id})
}
export class Service {
  async create(db: any, id: string, amount: number, active: boolean) {
    await db.account.create({data: {id, amount, active}})
  }
}
export class WithConstructor {
  constructor(_x: number) {}
  async create(db: any, id: string, amount: number, active: boolean) {
    await db.account.create({data: {id, amount, active}})
  }
}
export async function* generator(db: any, id: string, amount: number, active: boolean) {
  await db.account.create({data: {id, amount, active}})
  yield 1
}
export async function rest(db: any, ...id: string[]) {
  await db.account.findUnique({where: {id}})
}
export async function alias(db: any, id: string) {
  const client = db
  const row = await client.account.findUnique({where: {id}})
  return row.amount
}
export async function bad(db: any, amount: number) {
  await db.account.update({where: {amount}, data: {amount}})
}
