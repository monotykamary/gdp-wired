// @ts-ignore fixture intentionally does not install TypeORM
import {Entity, Column, PrimaryColumn} from 'typeorm'
@Entity()
export class Account {
  @PrimaryColumn() id!: string
  @Column() amount!: number
  @Column() active!: boolean
}
