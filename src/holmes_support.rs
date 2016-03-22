use holmes::pg::dyn::values::ValueT;
use holmes::pg::dyn::types::TypeT;
use bitvector::BitVector;
use std::any::Any;
use std::sync::Arc;
use postgres::types::ToSql;
use holmes::pg::RowIter;
use holmes::pg::dyn::{Type, Value};
use holmes::pg::dyn::values::ToValue;

#[derive(Debug,Clone,Hash)]
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
  fn inner(&self) -> &Any {
    self as &Any
  }
  fn inner_eq(&self, other : &TypeT) -> bool {
    other.inner().downcast_ref::<Self>().is_some()
  }
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
  fn inner(&self) -> &Any {
    self as &Any
  }
  fn inner_eq(&self, other : &ValueT) -> bool {
    match other.inner().downcast_ref::<Self>() {
      Some(x) => self == x,
      _ => false
    }
  }
  fn inner_ord(&self, other : &ValueT) -> Option<::std::cmp::Ordering> {
    other.inner().downcast_ref::<Self>().and_then(|x|self.partial_cmp(x))
  }
}

impl ToValue for BitVector {
  fn to_value(self) -> Value {
    Arc::new(self)
  }
}
