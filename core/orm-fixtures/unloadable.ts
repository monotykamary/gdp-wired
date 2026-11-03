// @ts-ignore fixture verifies that a failed original import refuses extraction
import './not-installed'
export async function create(db: any, id: string, amount: number, active: boolean) {
  await db.account.create({data: {id, amount, active}})
}
