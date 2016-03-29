use holmes::pg::dyn::values::ValueT;
use holmes::pg::dyn::types::TypeT;
use bitvector::BitVector;
use expert::Arch;
use std::any::Any;
use std::sync::Arc;
use postgres::types::ToSql;
use holmes::pg::RowIter;
use holmes::pg::dyn::{Type, Value};
use holmes::pg::dyn::values::ToValue;
use num::traits::FromPrimitive;

#[derive(Debug,Clone,Hash,PartialEq)]
pub struct BitVectorType;
impl TypeT for BitVectorType {
  fn name(&self) -> Option<&'static str> {
    Some("bitvector")
  }
  fn extract(&self, rows : &mut RowIter) -> Value {
    Arc::new(BitVector::new(&rows.next().unwrap()))
  }
  fn repr(&self) -> Vec<String> {
    vec!["bit varying".to_string()]
  }
  typet_boiler!();
}

impl ValueT for BitVector {
  fn type_(&self) -> Type {
    Arc::new(BitVectorType)
  }
  fn get(&self) -> &Any {
    self as &Any
  }
  fn to_sql(&self) -> Vec<&ToSql> {
    vec![self.to_bitvec()]
  }
  valuet_boiler!();
}

impl ToValue for BitVector {
  fn to_value(self) -> Value {
    Arc::new(self)
  }
}

#[derive(Debug,Clone,Hash,PartialEq)]
pub struct ArchType;
impl TypeT for ArchType {
  fn name(&self) -> Option<&'static str> {
    Some("arch")
  }
  fn extract(&self, rows : &mut RowIter) -> Value {
    Arc::new(Arch::from_i16(rows.next().unwrap()).unwrap())
  }
  fn repr(&self) -> Vec<String> {
    vec!["SMALLINT".to_string()]
  }
  typet_boiler!();
}

impl ValueT for Arch {
  fn type_(&self) -> Type {
    Arc::new(ArchType)
  }
  fn get(&self) -> &Any {
    self as &Any
  }
  fn to_sql(&self) -> Vec<&ToSql> {
    vec![self.i16_ref()]
  }
  valuet_boiler!();
}

impl ToValue for Arch {
  fn to_value(self) -> Value {
    Arc::new(self)
  }
}
